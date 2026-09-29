-- Prove2me | Theorems.Thm_UnramifiedWhittaker_exists_hasProd_eulerFactors_and_integral_zetaIntegrand_eq
-- name    : UnramifiedWhittaker.exists_hasProd_eulerFactors_and_integral_zetaIntegrand_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/b1a905d9-2241-5028-9af9-1006df607b30
-- title:
--   Euler product unfolding of an adelic GL₂ zeta integral
-- statement:
--   Let $F$ be a number field, $\mathbb{A}$ its adele ring, $\nu$ a measure on $\mathbb{A}^\times$ for a given measurable structure, $S$ a finite set of finite places, $\Phi$ a Hecke eigensystem over $\mathbb{C}$ (a nonzero level ideal together with families $a_v, b_v \in \mathbb{C}$ indexed by the finite places), $\chi : \mathbb{A}^\times \to \mathbb{C}^\times$ a group homomorphism, $W : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ a function, and for each finite place $v$ an additive character $\psi_v$ of $F_v$, an element $\varpi_v \in \mathcal{O}_v$ whose image in $F_v$ is nonzero, a finite nonempty index type $I_v$ and a family $b_{v,i} \in \mathcal{O}_v$. Assume, for every $v \notin S$: $\#I_v = Nv$, the absolute norm of $v$; the matrix $\mathrm{diag}(\varpi_v,1)$ placed in the $v$-component (all other components, and the infinite part, equal to $1$) equals $\mathrm{diag}(\varpi_v^{\mathrm{idele}},1)$, the Hecke generator built from the chosen uniformizer idele at $v$; $\psi_v$ is trivial on $\mathcal{O}_v$ and nontrivial on $\varpi_v^{-1}\mathcal{O}_v$; $W\bigl(\binom{1\ x}{0\ 1}_v g\bigr) = \psi_v(x) W(g)$ for $x \in F_v$; $W\bigl(g\binom{1\ r}{0\ 1}_v\bigr) = W(g)$ for $r \in \mathcal{O}_v$; the recursions $\sum_{i \in I_v} W\bigl(g\binom{\varpi_v\ b_{v,i}}{0\quad 1}_v\bigr) + W\bigl(g\binom{1\ 0}{0\ \varpi_v}_v\bigr) = a_v W(g)$ and $W\bigl(g\,(\varpi_v I_2)_v\bigr) = (Nv)^{-1} b_v\, W(g)$. Assume further that for every idele unit $u$ with trivial infinite part, trivial components at the places of $S$, and finite part integral with integral inverse at all places, one has $W(g\,\mathrm{diag}(u,1)) = W(g)$, $\chi(u) = 1$ and idele norm $\|u\| = 1$; that $\|\varpi_v^{\mathrm{idele}}\| = (Nv)^{-1}$ for all $v$; that $\|\chi(\varpi_v^{\mathrm{idele}})\| \le (Nv)^{\tau}$ and $\|a_v\|, \|b_v\| \le (Nv)^{\kappa}$ for $v \notin S$, with $\kappa \ge 0$; and that $\kappa + \tau + 4 \le \sigma_0$. Let $H_\nu$ be product-measure data for $S$ and $\nu$, providing a constant $c > 0$, a measure $\nu_S$, a projection and order functions with the stated decomposition, Tonelli and measurability properties, and assume the integrand $a \mapsto W(\mathrm{diag}(a,1))\,\chi(a)\,\|a\|^{s-1}$ is $\nu_S$-integrable whenever $\mathrm{Re}\,s > \sigma_0$. Then there is a function $L : \mathbb{C} \to \mathbb{C}$ such that for every $s$ with $\mathrm{Re}\,s > \sigma_0$ the family of inverses of the values at $(Nv)^{-s}$ of the polynomial $1 - \chi(\varpi_v^{\mathrm{idele}}) a_v X + \chi(\varpi_v^{\mathrm{idele}})^2 b_v X^2$ when $\chi$ is unramified at $v$ (meaning $\chi$ is trivial on the local units at $v$ embedded into $\mathbb{A}^\times$) and of the constant polynomial $1$ otherwise, indexed by the places $v \notin S$, has unconditional product $L(s)$; the integrand is $\nu$-integrable; and $\int \mathrm{d}\nu = c \cdot \bigl(\int \mathrm{d}\nu_S\bigr) \cdot L(s)$ for it.
--
--   This is the unfolding of a global zeta integral on $\mathrm{GL}_2$ over the ideles into the part at the places of $S$ times an Euler product over the remaining places, the hypotheses outside $S$ being those satisfied by the Whittaker function of a Hecke eigenform unramified outside $S$ (Jacquet–Langlands global theory), here formulated axiomatically for an arbitrary $W$, $\chi$ and measure decomposition. It feeds the construction of the twisted Euler product attached to an arithmetic genuine cuspidal realization and the measure-theoretic and synthesis steps of the converse-theorem package used for Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UnramifiedWhittaker_exists_hasProd_eulerFactors_and_integral_zetaIntegrand_eq.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_LocalLanglands_HeckeCosetLocal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix MeasureTheory Polynomial
open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdeleRing NumberField.TateGlobal
open AutomorphicForm AdelicDock

open scoped Classical in

theorem UnramifiedWhittaker.exists_hasProd_eulerFactors_and_integral_zetaIntegrand_eq
    (F : Type) [Field F] [NumberField F] [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] (ν : Measure (AdeleRing (𝓞 F) F)ˣ)
    (Φ : HeckeEigensystem F ℂ) (S : Finset (HeightOneSpectrum (𝓞 F))) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (W : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ)
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), AddChar (v.adicCompletion F) ℂ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F)
    (hπ : ∀ v : HeightOneSpectrum (𝓞 F),
      algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v) ≠ 0)
    {I : HeightOneSpectrum (𝓞 F) → Type*} [∀ v, Fintype (I v)] [∀ v, Nonempty (I v)]
    (b : ∀ v : HeightOneSpectrum (𝓞 F), I v → v.adicCompletionIntegers F)
    (hI : ∀ v ∉ S, Fintype.card (I v) = Ideal.absNorm v.asIdeal)
    (hgen : ∀ v ∉ S, finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (LocalGL2.diagPi (ϖ v) (hπ v))) = heckeGen (𝓞 F) F v)
    (hψ0 : ∀ v ∉ S, ∀ r : v.adicCompletionIntegers F,
      ψ v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r) = 1)
    (hψ1 : ∀ v ∉ S, ∃ r : v.adicCompletionIntegers F,
      ψ v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r /
        algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) ≠ 1)
    (hN : ∀ v ∉ S, ∀ (x : v.adicCompletion F) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)),
      W (placeEmbed F v (unipotent x) * g) = ψ v x * W g)
    (hK : ∀ v ∉ S, ∀ (r : v.adicCompletionIntegers F) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)),
      W (g * placeEmbed F v (unipotent
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r))) = W g)
    (hT : ∀ v ∉ S, ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F),
      (∑ i, W (g * placeEmbed F v (repSome
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v)
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (b v i))))) +
        W (g * placeEmbed F v (repInf
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v))) =
        Φ.a v * W g)
    (hZ : ∀ v ∉ S, ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F),
      W (g * placeEmbed F v (scalarPi
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v))) =
        Φ.toRawCentral.b v * W g)
    (hU : ∀ u : (AdeleRing (𝓞 F) F)ˣ,
      (u : AdeleRing (𝓞 F) F).1 = 1 →
      (∀ v ∈ S, (u : AdeleRing (𝓞 F) F).2 v = 1) →
      finitePartUnits (𝓞 F) F u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F →
      ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F), W (g * diagOne u) = W g)
    (hχU : ∀ u : (AdeleRing (𝓞 F) F)ˣ,
      (u : AdeleRing (𝓞 F) F).1 = 1 →
      (∀ v ∈ S, (u : AdeleRing (𝓞 F) F).2 v = 1) →
      finitePartUnits (𝓞 F) F u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F →
      χ u = 1)
    (hnormU : ∀ u : (AdeleRing (𝓞 F) F)ˣ,
      (u : AdeleRing (𝓞 F) F).1 = 1 →
      (∀ v ∈ S, (u : AdeleRing (𝓞 F) F).2 v = 1) →
      finitePartUnits (𝓞 F) F u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F →
      ideleNorm F u = 1)
    (hnorm : ∀ v : HeightOneSpectrum (𝓞 F),
      ideleNorm F (uniformizerIdele F v) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹)
    (τ : ℝ)
    (hτ : ∀ v ∉ S,
      ‖((χ (uniformizerIdele F v) : ℂˣ) : ℂ)‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ τ)
    (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hκ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      ‖Φ.a v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖Φ.b v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ)
    (σ₀ : ℝ) (hσ₀ : κ + τ + 4 ≤ σ₀)
    (Hν : ProductMeasureData S ν)
    (hS : ∀ s : ℂ, σ₀ < s.re → Integrable (zetaIntegrand W χ s) Hν.νS) :
    ∃ L : ℂ → ℂ, ∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
          ((if IsUnramifiedCharAt χ v.1
            then C 1 - C (((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) * Φ.a v.1) * X
              + C ((((χ (uniformizerIdele F v.1)) ^ 2 : ℂˣ) : ℂ) * Φ.b v.1) * X ^ 2
            else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (L s) ∧
        Integrable (zetaIntegrand W χ s) ν ∧
        (∫ a, zetaIntegrand W χ s a ∂ν) = Hν.c * (∫ a, zetaIntegrand W χ s a ∂Hν.νS) * L s := by sorry
