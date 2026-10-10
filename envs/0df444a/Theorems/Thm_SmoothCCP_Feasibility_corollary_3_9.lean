-- Prove2me | Theorems.Thm_SmoothCCP_Feasibility_corollary_3_9
-- name    : SmoothCCP.Feasibility.corollary_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:25.744996+00:00
-- url     : https://prove2.me/theorems/12ec2b8e-1522-4ce7-8078-3f05a1136430
-- title:
--   Corollary 3.9 — if C(x,ξ) has a pdf strictly decreasing on (−ε, ε) and F(0; x) < 1 − α, then β_x > 0 and ℙ(F^N_ε(0; x) ≥ 1 − α) ≤ exp{−2Nβ_x²}
-- statement:
--   Work in the setting of Theorem 3.8: $X\subseteq\mathbb R^n$ closed, $\alpha\in(0,1)$, admissible $\gamma_\varepsilon$, an i.i.d. sample $\xi_1,\dots,\xi_N$ ($N\ge1$) with law $\mathbb P_\xi$, and Assumption 3.1. Let $x\in X$ be such that $Y_x=C(x,\xi)$ is a continuous random variable with a probability density function $h_x$ that is strictly decreasing on the interval $(-\varepsilon,\varepsilon)$. If $F(0;x)<1-\alpha$, then
--   $$\beta_x:=F(0;x)-F_\varepsilon(0;x)>0\qquad\text{and}\qquad \mathbb P\bigl(F^N_\varepsilon(0;x)\ge 1-\alpha\bigr)\le\exp\{-2N\beta_x^2\}.$$
--
--   With no shift ($t=0$) and no tightening ($\delta=\alpha$), an infeasible point is still rejected by the smoothed sample test with probability exponentially close to one, provided the density of $C(x,\xi)$ is decreasing near $0$: the smoothed approximation is then conservative.
--
--   **Formalization Note** The density is encoded as $\mathbb P_\xi\circ C(x,\cdot)^{-1}=h_x\,d\lambda$ with $h_x\ge0$ measurable. Assumption 3.7 is not assumed: the corollary needs only $\beta_x>0$ at the one point $x$, which it proves. The statement is posed with the corollary's own hypotheses because the printed proof invokes Theorem 3.8, whose Assumption 3.7 is a condition on all of $X$.
-- source:
--   Peña-Ordieres, Luedtke, Wächter, Solving chance-constrained problems via a smooth sample-based nonlinear approximation, arXiv:1905.07377v2, Corollary 3.9, p. 12

import Mathlib
import Definitions.Def_SmoothCCP_Feasibility_Setting
open MeasureTheory

namespace SmoothCCP.Feasibility

theorem corollary_3_9 {n N : ℕ} {Ξ Ω : Type} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Fin N → Ω → Ξ) (hξ : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ P)
    (hlaw : ∀ i, P.map (ξ i) = Pξ) (hN : 1 ≤ N)
    (C : (Fin n → ℝ) → Ξ → ℝ) (X : Set (Fin n → ℝ)) (hX : IsClosed X)
    (hC : ∀ x ∈ X, Measurable (C x)) (hcont : ∀ x ∈ X, ∀ y : ℝ, Pξ {s | C x s = y} = 0)
    (α ε : ℝ) (γ : ℝ → ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hγ : AdmissibleGamma ε γ)
    (x : Fin n → ℝ) (hxX : x ∈ X)
    (h : ℝ → ℝ) (hh_meas : Measurable h) (hh_nonneg : ∀ y, 0 ≤ h y)
    (hdens : Pξ.map (C x) = volume.withDensity (fun y => ENNReal.ofReal (h y)))
    (hdec : StrictAntiOn h (Set.Ioo (-ε) ε))
    (hF : cdf Pξ C 0 x < 1 - α) :
    0 < cdf Pξ C 0 x - smoothCdf Pξ C ε γ 0 x ∧
      P {ω | 1 - α ≤ sampleCdf C ε γ (fun i => ξ i ω) 0 x}
        ≤ ENNReal.ofReal
            (Real.exp (-2 * (N : ℝ) * (cdf Pξ C 0 x - smoothCdf Pξ C ε γ 0 x) ^ 2)) := by sorry

end SmoothCCP.Feasibility
