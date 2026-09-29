-- Prove2me | Theorems.Thm_UnipotentTermUnfolding_exists_forall_integrableOn_and_lintegral_ne_top_and_setIntegral_unipotentTerm_eq_mul_integral_iwasawa_of_isSemiLocalFactorization
-- name    : UnipotentTermUnfolding.exists_forall_integrableOn_and_lintegral_ne_top_and_setIntegral_unipotentTerm_eq_mul_integral_iwasawa_of_isSemiLocalFactorization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/68f56836-99b7-5a66-a0ee-21483d037a4d
-- title:
--   Iwasawa unfolding of the unipotent term, semi-locally factorizable case
-- statement:
--   Let $K\subseteq L$ be number fields with $L/K$ Galois, and let $0<\alpha<\beta$ be real. Fix a Haar measure $\nu_{Z_L}$ on the idele group $(\mathbb{A}_L)^\times$ (with its Borel structure) and a fundamental domain $\Omega_L$ for the subgroup of principal ideles, the range of `Units.map` of $L\to\mathbb{A}_L$. Let $D$ be an `IdeleGaloisDescent` datum for $\mathcal{O}_L$, $K$, $L$ (a homomorphism from $\mathrm{Gal}(L/K)$ to continuous ring automorphisms of $\mathbb{A}_L$ compatible with the structure map), let $\sigma$ be an element with every $\tau\in\mathrm{Gal}(L/K)$ a power of $\sigma$, and let $\xi_L:\top\to\mathbb{C}^\times$ be a character of the full idele group which is continuous as a $\mathbb{C}$-valued function and trivial on principal ideles. Let $c>0$ and $u,d_1,d_2$ be real, $T_c$ a compact set in $\mathrm{GL}_2(\mathbb{A}_L)$, and $\Phi_0$ a set contained in $\bigcup_{y\in T_c}(\mathtt{centreCutSiegelSet}\,L\,c\,u\,d_1\,d_2)\,y$ and in the shell $\{g\mid \|\det g\|_{\mathbb{A}_L}\in[\alpha,\beta]\}$ (idele norm via the distributive Haar character), and which is a fundamental domain for the image of $\mathrm{GL}_2(L)$ acting on that shell with the adelic $\mathrm{GL}_2$ Haar measure restricted to it. Finally let $X$ be an additive fundamental domain for the principal adeles in $\mathbb{A}_L$ and $\Omega_1,\Omega_2$ fundamental domains for the principal ideles in $(\mathbb{A}_L)^\times$ with respect to `idelicHaar`. Then there is $\kappa\in(0,\infty)\subseteq[0,\infty]$ such that for every finite set $S'$ of finite places of $K$ and every $\varphi,\varphi_a,\varphi_f,(\varphi_v)_v$ satisfying `IsSemiLocalFactorization K L S'` (archimedean and finite test-function factors, locally constant compactly supported semi-local factors at $v\in S'$, the product formula for $\varphi_f$ off $S'$-integral elements, vanishing of $\varphi_f$ when some component off $S'$ is non-integral, and $\varphi(g)=\varphi_a(g_\infty)\varphi_f(g_{\mathrm{fin}})$), there is $R_1$ with the following holding for all $R\ge R_1$. Write $G_\varphi(x)=\int_{\Omega_L}\xi_L(z)\bigl(\sum_{\delta}\varphi(x^{-1}\,\delta\,{}^{\sigma_D}(z x))-\mathbf{1}_{\{H>e^R\}}\bigl(C(z x)\bigr)\bigr)\,d\nu_{Z_L}(z)$, where $\delta$ runs over those elements of $\mathrm{GL}_2(L)$ whose twisted $\sigma$-conjugacy class has `normClassMap` equal to the conjugacy class of some $\gamma\in\mathrm{GL}_2(K)$ of unipotent type (non-central with characteristic polynomial $(X-a)^2$), ${}^{\sigma_D}$ denotes `sigmaAdelicAct`, $H$ is the adelic height, and $C$ is the constant term, i.e. the integral over the adelic box with its conditional additive Haar measure of the unipotent translates of $y\mapsto\sum_{\delta}\varphi(x^{-1}\delta\,{}^{\sigma_D}y)$ over the $\delta\in\mathrm{GL}_2(L)$ with $\delta_{10}=0$ and $N_{L/K}(\delta_{00}/\delta_{11})=1$. Then: (i) $G_\varphi$ is integrable on $\Phi_0$ for the adelic $\mathrm{GL}_2$ Haar measure; (ii) the iterated lower integral over $x\in X$, $u\in\Omega_1$, $t\in\Omega_2$ and $k$ in the adelic maximal compact subgroup of the extended norm of the shell-indicator of $g\mapsto\int_{\Omega_L}\xi_L(z)\,(\mathtt{cuspKernel}-\mathtt{cuspTruncation}_R)(z,g)\,d\nu_{Z_L}$ evaluated at $n(x)\,z(u)\,\mathrm{diag}(t,1)\,k$, times $\|t\|^{-1}$, is finite; and (iii) $\int_{\Phi_0}G_\varphi = \kappa\cdot\int_X\int_{\Omega_1}\int_{\Omega_2}\int_{\mathbf{K}}$ of the same integrand (Bochner form). Here `cuspKernel` is the analogue of the first sum with $\delta$ further restricted to the upper-triangular subgroup, and `cuspTruncation` is the truncation term appearing in $G_\varphi$.
--
--   This is the unfolding of the unipotent-type contribution to the twisted (base-change) kernel for $\mathrm{GL}_2$ into Iwasawa coordinates $g=n(x)z(u)\mathrm{diag}(t,1)k$, together with the integrability and Tonelli finiteness needed to reorder the resulting iterated integral, stated for all test functions admitting a semi-local factorisation over a finite set of places of $K$. It is the form in which the unipotent term enters the rank-one reduction, and is cited by [`AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_sum_mul_setIntegral_rankOne_unram`](thm.html#AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_sum_mul_setIntegral_rankOne_unram).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UnipotentTermUnfolding_exists_forall_integrableOn_and_lintegral_ne_top_and_setIntegral_unipotentTerm_eq_mul_integral_iwasawa_of_isSemiLocalFactorization.lean

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
    UnipotentTermUnfolding.exists_forall_integrableOn_and_lintegral_ne_top_and_setIntegral_unipotentTerm_eq_mul_integral_iwasawa_of_isSemiLocalFactorization
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
      (NumberField.Idele.ideleBorel L) Ω₂ (NumberField.Idele.idelicHaar L)) :
    ∃ κ : ENNReal, κ ≠ 0 ∧ κ ≠ ⊤ ∧
    ∀ (S' : Finset (HeightOneSpectrum (𝓞 K))) (φ : AdelicGL2 (𝓞 L) L → ℂ)
      (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
      (φS' : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
      AutomorphicForm.IsSemiLocalFactorization K L S' φ φa φf φS' →
      ∃ R₁ : ℝ, ∀ R : ℝ, R₁ ≤ R →
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) _ _
          (@ProbabilityTheory.cond _ (NumberField.AdelicHaar.adeleBorel (𝓞 L) L)
            (adelicAddHaar (𝓞 L) L) (adelicBox L))
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      ∫⁻ x in X, ∫⁻ u in Ω₁, ∫⁻ t in Ω₂, ∫⁻ k,
            ‖Set.indicator
              ({g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} :
                Set (AdelicGL2 (𝓞 L) L))
              (fun g : AdelicGL2 (𝓞 L) L => ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                (TwistedBruhat.cuspKernel K L D σ hgen φ z g - TwistedBruhat.cuspTruncation K L D σ R φ z g) ∂νZL)
              (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
              (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)‖ₑ
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) ≠ ⊤ ∧
      (∫ x in Φ₀, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) _ _
          (@ProbabilityTheory.cond _ (NumberField.AdelicHaar.adeleBorel (𝓞 L) L)
            (adelicAddHaar (𝓞 L) L) (adelicBox L))
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L))
        = (κ.toReal : ℂ) * ∫ x in X, ∫ u in Ω₁, ∫ t in Ω₂, ∫ k,
            Set.indicator
              ({g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} :
                Set (AdelicGL2 (𝓞 L) L))
              (fun g : AdelicGL2 (𝓞 L) L => ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                (TwistedBruhat.cuspKernel K L D σ hgen φ z g - TwistedBruhat.cuspTruncation K L D σ R φ z g) ∂νZL)
              (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
              (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) := by sorry
