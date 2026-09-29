-- Prove2me | Theorems.Thm_TwistedUnipotentTerm_exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator
-- name    : TwistedUnipotentTerm.exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/ee71eab0-174e-5cb6-b86f-a5c5208334c4
-- title:
--   Truncated zeta integral affine in log X, local factors in its constant
-- statement:
--   Let $F$ be a number field, $\mu$ an additive Haar measure on the adele ring $\mathbb{A}_F$ (with its Borel structure) normalised so that $\mu$ of the adelic box — the set of adeles whose archimedean component lies in the preimage, under the identification with the mixed space, of the fundamental domain of the lattice basis of $F$, and whose finite component is integral at every finite place — equals $1$; let $\nu$ be a Haar measure on the idele group $\mathbb{A}_F^\times$ and $\Omega$ a fundamental domain for the subgroup of principal ideles, the range of $F^\times \to \mathbb{A}_F^\times$, acting on $\mathbb{A}_F^\times$ with respect to $\nu$. Fix finite sets $T \subseteq S$ of finite places (height-one primes of $\mathcal{O}_F$), additive Haar measures $\mu f_v$ on each completion $F_v$, a function $g$ on the infinite adeles, functions $h_{0,v}$ on the $F_v$, an index type $\Theta$, functions $h(\theta)_v$ on the $F_v$, and $\Psi : \Theta \to \mathbb{A}_F \to \mathbb{C}$ such that each $\Psi\,\theta$ is the indicator, on the set of adeles integral at every finite place outside $S$, of $x \mapsto g(x_\infty)\prod_{v \in S} k_v(x_v)$ with $k_v = h(\theta)_v$ for $v \in T$ and $k_v = h_{0,v}$ otherwise. Assume each $\Psi\,\theta$ lies in the Schwartz–Bruhat space (the $\mathbb{C}$-span of pure tensors of a Schwartz function on the mixed space with a locally constant compactly supported function on the finite adeles) and has compact support; that for every $\theta$ and $v \in T$ the local zeta function $s \mapsto Z_v(h(\theta)_v, s) = \int f\,|x|^s$ against the multiplicative Haar measure $\mathrm{d}\mu f_v/|x|$, with trivial character, is differentiable on $\{\mathrm{Re}\,s > 0\}$; and that for one index $\theta_0$ one has $\prod_{v \in T} Z_v(h(\theta_0)_v, 1) \neq 0$. Then there exist constants $c_0, c_1 \in \mathbb{C}$, independent of $\theta$ and of the cut-off, such that for every $\theta$ and every real $X > 0$ the function $$y \mapsto \|y\|^{-1}\Bigl(\textstyle\sum^{f}_{\eta \in F^\times} \Psi\,\theta\bigl(\eta \cdot y^{-1}\bigr) - \mathbf{1}_{\{X < \|y\|\}}\,\|y\|\int \Psi\,\theta\,\mathrm{d}\mu\Bigr),$$ where $\|y\|$ is the idele norm given by the distributive Haar character of $y$ on $\mathbb{A}_F$ and the sum is a finsum over $F^\times$, is integrable on $\Omega$ for $\nu$, and its integral over $\Omega$ equals $$\nu\bigl(\Omega \cap \{1 \le \|y\| \le e\}\bigr)\Bigl(\int \Psi\,\theta\,\mathrm{d}\mu\Bigr)\log X + c_0\prod_{v \in T} Z_v(h(\theta)_v,1) + c_1\Bigl(\int \Psi\,\theta_0\,\mathrm{d}\mu\Bigr)\sum_{p \in T} Z_p'(h(\theta)_p,1)\prod_{v \in T,\ v \neq p} Z_v(h(\theta)_v,1),$$ the derivative being taken in $s$ at $s = 1$. Note that the coefficient $c_1$ is multiplied by the integral of $\Psi\,\theta_0$ at the distinguished index $\theta_0$, not of $\Psi\,\theta$.
--
--   This is a Tate-style evaluation of a truncated rank-one zeta integral over a fundamental domain for the principal ideles: the truncated integral is an affine function of $\log X$ whose slope is the volume of a unit-norm slab times the total integral of the test function, and whose constant term is a linear combination of the product of the local zeta values at $s = 1$ over $T$ and of its logarithmic derivative. It feeds the uniform variant [`TwistedUnipotentTerm.exists_forall_exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator_uniform`](thm.html#TwistedUnipotentTerm.exists_forall_exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator_uniform), where the constants are made independent of the remaining data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwistedUnipotentTerm_exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator.lean

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
    TwistedUnipotentTerm.exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator
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
    (g : InfiniteAdeleRing F → ℂ)
    (h₀ : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (Θ : Type) (h : Θ → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (Ψ : Θ → AdeleRing (𝓞 F) F → ℂ)
    (hΨ : ∀ θ x, Ψ θ x = (NumberField.TateGlobal.integralOutside S).indicator
      (fun x => g x.1 * ∏ v ∈ S, (if v ∈ T then h θ v else h₀ v) ((x.2 : FiniteAdeleRing (𝓞 F) F) v)) x)
    (hΨs : ∀ θ, Ψ θ ∈ NumberField.AdelicFourier.schwartzBruhat F) (hΨc : ∀ θ, HasCompactSupport (Ψ θ))
    (hloc : ∀ θ, ∀ v ∈ T, DifferentiableOn ℂ
      (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf v) (h θ v) 1 s) {s : ℂ | 0 < s.re})
    (θ₀ : Θ) (hθ₀ : ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ₀ i) 1 1 ≠ 0) :
    ∃ c₀ c₁ : ℂ, ∀ θ : Θ, ∀ X : ℝ, 0 < X →
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
