-- Prove2me | Theorems.Thm_UnipotentTermUnfolding_forall_exists_lintegral_iwasawa_tsum_tsum_enorm_sub_ne_top_of_isSemiLocalFactorization
-- name    : UnipotentTermUnfolding.forall_exists_lintegral_iwasawa_tsum_tsum_enorm_sub_ne_top_of_isSemiLocalFactorization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/6ed137ff-0d49-5de5-8351-19c624742049
-- title:
--   Fibrewise finiteness of the unipotent term in Iwasawa coordinates
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, and let $0 < \alpha < \beta$ be reals. Fix a Haar measure $\nu_{Z_L}$ on the idele group $(\mathbb{A}_L)^\times$ and a set $\Omega_L$ that is a fundamental domain for the subgroup of principal ideles acting on $(\mathbb{A}_L)^\times$ with respect to $\nu_{Z_L}$. Let $D$ be an idele Galois descent datum for $L/K$, i.e. a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$ that is continuous and compatible with the action on $L$ via the structure map; let $\sigma$ be an element of $\mathrm{Gal}(L/K)$ whose integral powers exhaust the group; and let $\xi_L$ be a homomorphism from the full subgroup of $(\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$ which is continuous as a $\mathbb{C}$-valued function and trivial on principal ideles. Let $c, u, d_1, d_2$ be reals with $c > 0$, let $T_c$ be a compact subset of $\mathrm{GL}_2(\mathbb{A}_L)$, and let $\Phi_0$ be contained in the union of the right translates by elements of $T_c$ of the centre-cut Siegel set for these parameters (finite part integral, local height at least $c$ and $x$-window at most $u^2$ at every infinite place, archimedean determinant norms in $[d_1, d_2]$) and in the slab where the idele norm of the determinant lies in $[\alpha, \beta]$, and be a fundamental domain for the left action of the image of $\mathrm{GL}_2(L)$ on $\mathrm{GL}_2(\mathbb{A}_L)$ for the adelic Haar measure restricted to that slab. Finally let $X$ be an additive fundamental domain for the principal subgroup of $\mathbb{A}_L$ with respect to adelic additive Haar measure, and $\Omega_1, \Omega_2$ fundamental domains for the principal ideles in $(\mathbb{A}_L)^\times$ with respect to idelic Haar measure. The assertion is: for every finite set $S'$ of height-one primes of $\mathcal{O}_K$ and all functions $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$, $\varphi_a$ on $\mathrm{GL}_2$ of the infinite adeles, $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles and $\varphi_{S'}(v)$ on $\mathrm{GL}_2(L \otimes_K K_v)$ satisfying `IsSemiLocalFactorization` for $S'$ — that is, $\varphi_a$ is smooth in the mixed-space matrix entries and compactly supported, $\varphi_f$ is locally constant with compact support, each $\varphi_{S'}(v)$ for $v \in S'$ is locally constant with compact support, $\varphi_f(h) = \prod_{v \in S'} \varphi_{S'}(v)$ of the semi-local component of $h$ whenever all components outside $S'$ are integral, $\varphi_f(h) = 0$ as soon as some component outside $S'$ is not integral, and $\varphi(g) = \varphi_a(g_\infty)\varphi_f(g_{\mathrm{fin}})$ — there exists $R_1 \in \mathbb{R}$ such that for every $R \ge R_1$ the iterated lower integral over $x \in X$, $u \in \Omega_1$, $t \in \Omega_2$ and $k$ in the adelic maximal compact subgroup, of $\mathrm{ofReal}\,|t|^{-1}$ times the indicator of the determinant slab $[\alpha,\beta]$ applied at $g = n(x)\,z(u)\,\mathrm{diag}(t,1)\,k$ of the function
--   $$g \mapsto \int^{-}_{\Omega_L} \|\xi_L(z)\|_e \sum_{s \in L^\times} \ \sum_{a \in L^\times,\ N_{L/K}(a) = 1} \bigl\| A_{s,a}(z,g) - B_{s,a}(z,g) \bigr\|_e \, d\nu_{Z_L}(z),$$
--   is not $\infty$. Here $A_{s,a}(z,g)$ is the finite sum over those $\delta \in \mathrm{GL}_2(L)$ lying in the twisted-norm unipotent set (those whose $\sigma$-twisted conjugacy class has norm class equal to the conjugacy class of some unipotent-type $\gamma \in \mathrm{GL}_2(K)$) with $\delta_{10} = 0$, $\delta_{11} = s$ and $\delta_{00} = sa$, of $\varphi(g^{-1}\,\delta\,\sigma_D(z g))$, where $\sigma_D$ is the entrywise action of $D(\sigma)$ and $z$ acts as a central scalar; and $B_{s,a}(z,g)$ is the value at $z g$ of the indicator of the set where the adelic height exceeds $\exp R$ times the constant term along the unipotent subgroup $t \mapsto n(t)$, taken with respect to the additive adelic Haar measure conditioned on the adelic box, of the function $y \mapsto$ the finite sum over the $\delta$ with $\delta_{10} = 0$, $\delta_{11} = s$, $\delta_{00} = sa$ (no twisted-norm condition) of $\varphi(g^{-1}\,\delta\,\sigma_D(y))$.
--
--   This is the absolute (Tonelli) finiteness, fibre by fibre in Iwasawa coordinates $g = n(x)z(u)\mathrm{diag}(t,1)k$, of the truncated unipotent-type contribution to the $\sigma$-twisted kernel: the extended norms sit inside the sums over the parameters $s$ and the norm-one ratios $a$, so that those sums may be integrated term by term against $\Omega_2$. It is the form of the cusp bound used by [`AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_sum_mul_setIntegral_rankOne_unram`](thm.html#AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_sum_mul_setIntegral_rankOne_unram) in the descent of the unipotent term to rank-one orbital integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UnipotentTermUnfolding_forall_exists_lintegral_iwasawa_tsum_tsum_enorm_sub_ne_top_of_isSemiLocalFactorization.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel
open IsDedekindDomain
open scoped TensorProduct

theorem
    UnipotentTermUnfolding.forall_exists_lintegral_iwasawa_tsum_tsum_enorm_sub_ne_top_of_isSemiLocalFactorization
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (X : Set (AdeleRing (𝓞 L) L)) (Ω₁ Ω₂ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hX : @IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) _ _ _
      (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    (hΩ₁ : @IsFundamentalDomain (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range _ _ _
      (NumberField.Idele.ideleBorel L) Ω₁ (NumberField.Idele.idelicHaar L))
    (hΩ₂ : @IsFundamentalDomain (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range _ _ _
      (NumberField.Idele.ideleBorel L) Ω₂ (NumberField.Idele.idelicHaar L))  :
    ∀ (S' : Finset (HeightOneSpectrum (𝓞 K))) (φ : AdelicGL2 (𝓞 L) L → ℂ)
      (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
      (φS' : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
      AutomorphicForm.IsSemiLocalFactorization K L S' φ φa φf φS' →
      ∃ R₁ : ℝ, ∀ R : ℝ, R₁ ≤ R →
      ∫⁻ x in X, ∫⁻ u in Ω₁, ∫⁻ t in Ω₂, ∫⁻ k,
            Set.indicator
              ({g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} :
                Set (AdelicGL2 (𝓞 L) L))
              (fun g : AdelicGL2 (𝓞 L) L => ∫⁻ z in ΩL, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
                ∑' s : Lˣ, ∑' a : {α : Lˣ // Algebra.norm K (α : L) = 1},
              ‖(∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L)},
                  φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L z * g))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L)},
                    φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L z * g)‖ₑ ∂νZL)
              (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
              ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) ≠ ⊤ := by sorry
