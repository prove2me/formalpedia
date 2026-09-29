-- Prove2me | Theorems.Thm_TwistedUnipotentTerm_exists_transversal
-- name    : TwistedUnipotentTerm.exists_transversal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/8b46ba81-04bb-5406-a32d-b046f51dde7a
-- title:
--   Transversal measures on the ideles of an extension L/K
-- statement:
--   Let $K$ and $L$ be number fields with a $K$-algebra structure on $L$, let $S_L$ be a finite set of primes of $\mathcal O_L$ containing every $w$ whose ramification index $e(w/w\cap\mathcal O_K)$ is $\neq 1$, and let $S,T$ be finite sets of primes of $\mathcal O_K$ (the conclusion does not refer to $S_L$). Then there exist a finite set $S_\tau$ of primes of $\mathcal O_K$, an $n\in\mathbb N$, reals $c_j$, measures $\tau_j$ on the idele class group-free idele unit group $(\mathbb A_L)^\times$, for each $j$ and each finite place $v$ of $K$ a measure $\tau^{\mathrm{fin}}_{j,v}$ on $(L\otimes_K K_v)^\times$ and a unit $\pi_{j,v}\in (L\otimes_K K_v)^\times$, for each $j$ and each infinite place $v$ of $K$ a measure $\tau^{\mathrm{arch}}_{j,v}$ on $(\prod_{w\mid v}L_w)^\times$, and $c_\tau\in[0,\infty]$, such that: $v\in S_\tau$ exactly when $v\in S$, $v\notin T$, or some $w$ above $v$ has ramification index $\neq 1$; $c_\tau\neq 0,\infty$ and each $c_j>0$; each $\tau_j$ is finite on compacta and vanishes off $\{t:\lVert t\rVert=c_j\}$, where $\lVert\cdot\rVert$ is the idelic norm given by the module character of the action on $\mathbb A_L$. The set $\mathrm{saturated}\,K\,L\,S_\tau$ of ideles $t$ whose semi-local component at every $v\notin S_\tau$ lies in `saturatedUnits K L v` is measurable, stable under multiplication by the base change of any idele of $K$, and carries all the $\tau_j$; for every measurable $E$ inside it, $s\mapsto(\sum_j\tau_j)(E\cdot(\text{base change of }s)^{-1})$ is measurable and $\mathrm{haar}_L(E)=c_\tau\int^-(\sum_j\tau_j)(E\cdot(\text{base change of }s)^{-1})\,d\,\mathrm{haar}_K$. Locally: for $v\notin S_\tau$, $\tau^{\mathrm{fin}}_{j,v}$ is a Haar measure normalised and restricted to the unit subgroup $\mathrm{integralUnits}\,K\,L\,v$ coming from $\mathcal O_L\otimes\mathcal O_{K_v}$, hence a probability measure concentrated there; for $v\in S_\tau$, $\tau^{\mathrm{fin}}_{j,v}$ is the translate by $\pi_{j,v}$ of the image of a Haar measure on the kernel $\mathrm{normOneUnits}\,K\,L\,v$ of $\mathrm{val}_v\circ N_{(L\otimes K_v)/K_v}$; $c_j=\prod_{v\in S_\tau}(\#\mathcal O_K/v)^{\log\mathrm{val}_v(N(\pi_{j,v}))}$; each $\tau^{\mathrm{arch}}_{j,v}$ is the image of a Haar measure on the kernel $\mathrm{archNormOneUnits}\,K\,L\,v$ of $|\cdot|\circ N$. Finally, for each $j$ and each finite $S_f\supseteq S_\tau$ and measurable $[0,\infty]$-valued $f_v$ ($v\in S_f$) and $g_v$ (all infinite $v$), the $\tau_j$-integral of $\prod_v g_v(\text{arch component})\cdot\prod_{v\in S_f}f_v(\text{semi-local component})$ cut off by the indicator of the ideles integral at all $v\notin S_f$ equals $\prod_v\int g_v\,d\tau^{\mathrm{arch}}_{j,v}\cdot\prod_{v\in S_f}\int f_v\,d\tau^{\mathrm{fin}}_{j,v}$.
--
--   This is the construction of the transversal (orbital) measures that decompose idelic Haar measure on $(\mathbb A_L)^\times$ along the base-change image of $(\mathbb A_K)^\times$, together with a factorisation of each transversal measure into local measures supported on norm-one cosets. It is used in the analysis of the twisted unipotent term, and is cited in the evaluation of the difference between the cuspidal kernel and its truncation as a sum of rank-one contributions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwistedUnipotentTerm_exists_transversal.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_TransversalMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open AutomorphicForm.TransversalMeasure
open scoped TensorProduct
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel in
attribute [local instance] AutomorphicForm.TransversalMeasure.semiLocalUnitsBorel
  AutomorphicForm.TransversalMeasure.archUnitsBorel in
open scoped TensorProduct.RightActions in

theorem TwistedUnipotentTerm.exists_transversal
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L),
      (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1 → w ∈ SL)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (Sτ : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (c : Fin n → ℝ) (τ : Fin n → Measure (AdeleRing (𝓞 L) L)ˣ)
      (τfin : Fin n → ∀ v : HeightOneSpectrum (𝓞 K), Measure (L ⊗[K] v.adicCompletion K)ˣ)
      (τarch : Fin n → ∀ v : InfinitePlace K, Measure (∀ w : v.Extension L, w.1.Completion)ˣ)
      (πs : Fin n → ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ) (cτ : ENNReal),

      (∀ v : HeightOneSpectrum (𝓞 K), v ∈ Sτ ↔ (v ∈ S ∧ v ∉ T) ∨
        ∃ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v ∧
          (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1) ∧

      cτ ≠ 0 ∧ cτ ≠ ⊤ ∧ (∀ j, 0 < c j) ∧

      (∀ j, τ j {t | NumberField.TateGlobal.ideleNorm L t ≠ c j} = 0) ∧ (∀ j, IsFiniteMeasureOnCompacts (τ j)) ∧

      MeasurableSet (saturated K L Sτ) ∧
      (∀ t ∈ saturated K L Sτ, ∀ s : (AdeleRing (𝓞 K) K)ˣ, t * idelesBaseChange K L s ∈ saturated K L Sτ) ∧
      (∀ j, τ j (saturated K L Sτ)ᶜ = 0) ∧
      (∀ E : Set (AdeleRing (𝓞 L) L)ˣ, MeasurableSet E → E ⊆ saturated K L Sτ →
        Measurable (fun s : (AdeleRing (𝓞 K) K)ˣ =>
          (∑ j, τ j) ((fun t => t * idelesBaseChange K L s) ⁻¹' E)) ∧
        NumberField.Idele.idelicHaar L E = cτ *
          ∫⁻ s : (AdeleRing (𝓞 K) K)ˣ, (∑ j, τ j) ((fun t => t * idelesBaseChange K L s) ⁻¹' E)
            ∂(NumberField.Idele.idelicHaar K)) ∧

      (∀ j (v : HeightOneSpectrum (𝓞 K)), v ∉ Sτ → ∃ μ : Measure (L ⊗[K] v.adicCompletion K)ˣ, μ.IsHaarMeasure ∧
        τfin j v = (μ (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ))⁻¹ •
          μ.restrict (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)) ∧
      (∀ j (v : HeightOneSpectrum (𝓞 K)), v ∉ Sτ →
        τfin j v (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)ᶜ = 0 ∧
          τfin j v (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) = 1) ∧

      (∀ j (v : HeightOneSpectrum (𝓞 K)), v ∈ Sτ → ∃ μN : Measure (normOneUnits K L v), μN.IsHaarMeasure ∧
        τfin j v = Measure.map (fun x => πs j v * x) (Measure.map Subtype.val μN)) ∧

      (∀ j, c j = ∏ v ∈ Sτ, (Ideal.absNorm v.asIdeal : ℝ) ^ WithZero.log (Valued.v
        ((Algebra.norm (v.adicCompletion K) : L ⊗[K] v.adicCompletion K →* v.adicCompletion K)
          (πs j v : L ⊗[K] v.adicCompletion K)))) ∧

      (∀ j (v : InfinitePlace K), ∃ μN : Measure (archNormOneUnits K L v), μN.IsHaarMeasure ∧
        τarch j v = Measure.map Subtype.val μN) ∧

      ∀ j (Sf : Finset (HeightOneSpectrum (𝓞 K))), Sτ ⊆ Sf →
        ∀ (f : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ENNReal)
          (g : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ → ENNReal),
          (∀ v ∈ Sf, Measurable (f v)) → (∀ v, Measurable (g v)) →
          ∫⁻ t, (∏ v : InfinitePlace K, g v (archSemiLocalIdele K L v t)) *
              (∏ v ∈ Sf, f v (semiLocalIdele K L v t)) *
              Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf → semiLocalIdele K L v t ∈ integralUnits K L v}
                (fun _ => (1 : ENNReal)) t ∂(τ j) =
            (∏ v : InfinitePlace K, ∫⁻ x, g v x ∂(τarch j v)) * ∏ v ∈ Sf, ∫⁻ x, f v x ∂(τfin j v) := by sorry
