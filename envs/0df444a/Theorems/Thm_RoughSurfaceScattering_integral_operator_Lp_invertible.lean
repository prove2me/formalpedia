-- Prove2me | Theorems.Thm_RoughSurfaceScattering_integral_operator_Lp_invertible
-- name    : RoughSurfaceScattering.integral_operator_Lp_invertible
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:57:05.899325+00:00
-- url     : https://prove2.me/theorems/61ee7d8e-4890-4677-a36f-24abfc6b8a7a
-- title:
--   Remark 4.4: $\mathcal M$ is bijective and boundedly invertible on $[L^p(\Gamma)]^2$
-- statement:
--   Under the hypotheses of Theorem 4.3 ($f\in BC^{1,1}(\mathbb R)$, $k_\pm,\mu>0$, $(\mu-1)(k_+^2-k_-^2\mu)\ge0$, $k_+^2\ne k_-^2\mu$, $h_-<f^-<f^+<h_+$), let $1\le p\le\infty$ and let $L^p(\Gamma)$ be taken with respect to arc length. Then the operator $\mathcal M$ of (4.14) is bijective and boundedly invertible on $[L^p(\Gamma)]^2$:
--
--   1. $\mathcal M$ maps $[L^p(\Gamma)]^2$ into itself;
--   2. for every $G\in[L^p(\Gamma)]^2$ there is $\chi\in[L^p(\Gamma)]^2$ with $\mathcal M\chi=G$ almost everywhere;
--   3. if $\chi,\chi'\in[L^p(\Gamma)]^2$ and $\mathcal M\chi=\mathcal M\chi'$ almost everywhere, then $\chi=\chi'$ almost everywhere;
--   4. there is $C$ with $\|\varphi\|_{L^p}+\|\psi\|_{L^p}\le C\big(\|(\mathcal M\chi)_1\|_{L^p}+\|(\mathcal M\chi)_2\|_{L^p}\big)$ for all $\chi=(\varphi,\psi)\in[L^p(\Gamma)]^2$.
--
--   The abstract calls this the $L^p$ well-posedness; it is used for $1\le p<\infty$ in the proof of Theorem 5.2.
--
--   **Formalization Note** Elements of $L^p$ are represented by functions, so equalities are almost everywhere. The bounded inverse is stated as the a priori bound in item 4.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, claim c004; Section 4, Remark 4.4 (on eq. (4.14)), PDF p. 17

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem integral_operator_Lp_invertible (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
    (kp km μ : ℝ) (hpar : ParamCond kp km μ)
    (hm hp : ℝ) (hh : hm < finf f ∧ finf f < fsup f ∧ fsup f < hp)
    (p : ENNReal) (hp1 : 1 ≤ p) :
    (∀ φ ψ : ℝ → ℂ, MemLp φ p (arcMeasure f) → MemLp ψ p (arcMeasure f) →
      MemLp (Mop f kp km μ hm hp φ ψ).1 p (arcMeasure f) ∧
        MemLp (Mop f kp km μ hm hp φ ψ).2 p (arcMeasure f)) ∧
    (∀ G1 G2 : ℝ → ℂ, MemLp G1 p (arcMeasure f) → MemLp G2 p (arcMeasure f) →
      ∃ φ ψ : ℝ → ℂ, MemLp φ p (arcMeasure f) ∧ MemLp ψ p (arcMeasure f) ∧
        (Mop f kp km μ hm hp φ ψ).1 =ᵐ[arcMeasure f] G1 ∧
        (Mop f kp km μ hm hp φ ψ).2 =ᵐ[arcMeasure f] G2) ∧
    (∀ φ ψ φ' ψ' : ℝ → ℂ, MemLp φ p (arcMeasure f) → MemLp ψ p (arcMeasure f) →
      MemLp φ' p (arcMeasure f) → MemLp ψ' p (arcMeasure f) →
      (Mop f kp km μ hm hp φ ψ).1 =ᵐ[arcMeasure f] (Mop f kp km μ hm hp φ' ψ').1 →
      (Mop f kp km μ hm hp φ ψ).2 =ᵐ[arcMeasure f] (Mop f kp km μ hm hp φ' ψ').2 →
      φ =ᵐ[arcMeasure f] φ' ∧ ψ =ᵐ[arcMeasure f] ψ') ∧
    ∃ C : ℝ, ∀ φ ψ : ℝ → ℂ, MemLp φ p (arcMeasure f) → MemLp ψ p (arcMeasure f) →
      eLpNorm φ p (arcMeasure f) + eLpNorm ψ p (arcMeasure f) ≤
        ENNReal.ofReal C * (eLpNorm (Mop f kp km μ hm hp φ ψ).1 p (arcMeasure f) +
          eLpNorm (Mop f kp km μ hm hp φ ψ).2 p (arcMeasure f)) := by sorry

end RoughSurfaceScattering
