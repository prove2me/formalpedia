-- Prove2me | Theorems.Thm_TwistedUnipotentTerm_exists_forall_exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator_uniform
-- name    : TwistedUnipotentTerm.exists_forall_exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator_uniform
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/13b8f1e5-6938-5aeb-bdfc-6f7bb4f188f3
-- title:
--   Truncated Tate integral, affine in log X, uniform derivative coefficient
-- statement:
--   Let $F$ be a number field, let $\mu$ be an additive Haar measure on the adele ring $\mathbb{A}_F$ with $\mu$ of the adelic box (the set of adeles whose infinite part lies in the preimage under `InfiniteAdeleRing.ringEquiv_mixedSpace` of the fundamental domain of the lattice basis of the mixed space, and whose finite part is integral at every place) equal to $1$, let $\nu$ be a Haar measure on the idele group and let $\Omega$ be a fundamental domain for the action of the range of $F^\times \to \mathbb{A}_F^\times$ on the ideles with respect to $\nu$. Let $T \subseteq S$ be finite sets of finite places, let $\mu f_v$ be additive Haar measures on the completions $F_v$, let $\Theta$ be a type and $h$ assign to $\theta \in \Theta$ and a finite place $v$ a function $h_\theta^v : F_v \to \mathbb{C}$, such that for all $\theta$ and all $v \in T$ the local zeta integral $s \mapsto Z_v(h_\theta^v, 1, s) = \int h_\theta^v(x)\,|x|^s \, d(\mu f_v)^\times(x)$ (with trivial character, the multiplicative measure being $\mu f_v$ restricted to $x \neq 0$ weighted by $|x|^{-1}$, $|x|$ the module of $x$) is differentiable on $\{\operatorname{Re} s > 0\}$, and such that for some $\theta_0$ one has $\prod_{v \in T} Z_v(h_{\theta_0}^v, 1, 1) \neq 0$. Then there is a constant $c_1 \in \mathbb{C}$ — chosen before, hence independent of, the data $g, h_0, \Psi$ below — such that for every $g : \mathbb{A}_{F,\infty} \to \mathbb{C}$, every family $h_0$ of functions $F_v \to \mathbb{C}$ and every family $\Psi : \Theta \to \mathbb{A}_F \to \mathbb{C}$ with $\Psi_\theta$ equal to the indicator, on the set of adeles integral at all $v \notin S$, of $x \mapsto g(x_\infty)\prod_{v \in S} (h_\theta^v \text{ if } v \in T, \text{ else } h_0^v)(x_v)$, each $\Psi_\theta$ lying in the Schwartz–Bruhat space (the $\mathbb{C}$-span of pure tensors $g \otimes h$ with $g$ Schwartz on the mixed space and $h$ locally constant of compact support on the finite adeles) and compactly supported, there exists $c_0 \in \mathbb{C}$ such that for every $\theta$ and every real $X > 0$ the function $y \mapsto \|y\|^{-1}\bigl(\sum_{\eta \in F^\times}^{\mathrm{f}} \Psi_\theta(\eta y^{-1}) - \mathbf 1_{X < \|y\|}\,\|y\| \int \Psi_\theta \, d\mu\bigr)$, with $\|y\|$ the idele norm given by the distributive Haar character, is integrable on $\Omega$ for $\nu$ and its integral over $\Omega$ equals $$\nu\bigl(\Omega \cap \{1 \le \|y\| \le e\}\bigr)\Bigl(\int \Psi_\theta \, d\mu\Bigr)\log X + c_0 \prod_{v \in T} Z_v(h_\theta^v,1,1) + c_1 \Bigl(\int \Psi_{\theta_0} \, d\mu\Bigr) \sum_{p \in T} Z_p'(h_\theta^p,1,1)\prod_{v \in T,\, v \neq p} Z_v(h_\theta^v,1,1),$$ where $Z_p'$ denotes the derivative in $s$ at $s = 1$.
--
--   This is the truncated rank-one global Tate integral over a fundamental domain for the principal ideles, evaluated for a factorisable test function: the result is affine in $\log X$ with leading coefficient the volume of the norm-one-to-$e$ slab times the total mass, and a constant term built from the product of the local zeta values at $s=1$ at the places of $T$ together with its logarithmic derivative. It sharpens the quantifier order of [`TwistedUnipotentTerm.exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator`](thm.html#TwistedUnipotentTerm.exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator) by producing the coefficient $c_1$ of the derivation term before the archimedean factor $g$ and the auxiliary factors $h_0$ at $S \setminus T$ are given, which permits finite sums of such families; it is used in the computation of the unipotent contribution in [`AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_mul_localZeta_twistedLocalFactor_unram`](thm.html#AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_mul_localZeta_twistedLocalFactor_unram).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwistedUnipotentTerm_exists_forall_exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator_uniform.lean

import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem
    TwistedUnipotentTerm.exists_forall_exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator_uniform
    (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (hμ1 : μ (NumberField.AdelicBox.adelicBox F) = 1)
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : T ⊆ S)
    (Θ : Type) (h : Θ → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hloc : ∀ θ, ∀ v ∈ T, DifferentiableOn ℂ
      (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf v) (h θ v) 1 s) {s : ℂ | 0 < s.re})
    (θ₀ : Θ) (hθ₀ : ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ₀ i) 1 1 ≠ 0) :
    ∃ c₁ : ℂ, ∀ (g : InfiniteAdeleRing F → ℂ) (h₀ : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
      (Ψ : Θ → AdeleRing (𝓞 F) F → ℂ),
      (∀ θ x, Ψ θ x = (NumberField.TateGlobal.integralOutside S).indicator
        (fun x => g x.1 * ∏ v ∈ S, (if v ∈ T then h θ v else h₀ v) ((x.2 : FiniteAdeleRing (𝓞 F) F) v)) x) →
      (∀ θ, Ψ θ ∈ NumberField.AdelicFourier.schwartzBruhat F) → (∀ θ, HasCompactSupport (Ψ θ)) →
    ∃ c₀ : ℂ, ∀ θ : Θ, ∀ X : ℝ, 0 < X →
      IntegrableOn (fun y : (AdeleRing (𝓞 F) F)ˣ =>
        ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
          ((∑ᶠ η : Fˣ, Ψ θ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
              AdeleRing (𝓞 F) F))) -
            (if X < NumberField.TateGlobal.ideleNorm F y then
              ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ θ u ∂μ else 0))) Ω ν ∧
      (∫ y in Ω,
        ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
          ((∑ᶠ η : Fˣ, Ψ θ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
              AdeleRing (𝓞 F) F))) -
            (if X < NumberField.TateGlobal.ideleNorm F y then
              ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ θ u ∂μ else 0)) ∂ν) =
        ((ν (Ω ∩ {y | 1 ≤ NumberField.TateGlobal.ideleNorm F y ∧
            NumberField.TateGlobal.ideleNorm F y ≤ Real.exp 1})).toReal : ℂ) *
          (∫ u, Ψ θ u ∂μ) * (Real.log X : ℂ) +
        (c₀ * ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ i) 1 1 +
          c₁ * (∫ u, Ψ θ₀ u ∂μ) *
            ∑ p : T, deriv (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf p) (h θ p) 1 s) 1 *
              ∏ i ∈ Finset.univ.erase p, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ i) 1 1) := by sorry
