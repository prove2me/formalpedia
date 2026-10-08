-- Prove2me | Theorems.Thm_TimeInconsLQ_MeanVariance_proposition_5_3
-- name    : TimeInconsLQ.MeanVariance.proposition_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:24:07.514986+00:00
-- url     : https://prove2.me/theorems/e59913b7-76a1-492e-b19e-50e894a54257
-- title:
--   Proposition 5.3 — the closed-loop wealth under the feedback (5.14) exists with continuous paths, E sup|X*|² < ∞, and u* ∈ L²
-- statement:
--   In the market of §5, let $(M,U)$ solve (5.8) in the class of Proposition 5.1 and $(\Gamma^{(2)},\gamma^{(2)})$ solve (5.13) in the class of Proposition 5.2, and define the feedback (5.14)
--   $$\alpha_s=\frac{\Gamma^{(1)}_s\theta_s-U_s}{M_s},\qquad\beta_s=-\frac{\Gamma_s\theta_s+\gamma^{(2)}_s}{M_s},\qquad u^*_s=\alpha_sX^*_s+\beta_s .$$
--   Then the closed-loop wealth equation (first line of (5.4))
--   $$dX^*_s=[r_sX^*_s+\theta_s'u^*_s]\,ds+(u^*_s)'\,dW_s,\qquad X^*_0=x_0,$$
--   has a solution $X^*$ whose paths are almost surely continuous on $[0,T]$, with
--   $$E\Big[\sup_{t\in[0,T]}|X^*_t|^2\Big]<\infty,$$
--   and $u^*\in L^2_{\mathcal F}(0,T;\mathbb R^d)$.
--
--   The gain $\alpha$ is in general unbounded ($U$ is only BMO), so admissibility of $u^*$ is not automatic; this proposition supplies it.
--
--   **Formalization Note.** The paper says "Let $X^*$ be the solution … Then $X^*\in L^2_{\mathcal F}(0,T;C(0,T;\mathbb R))$ and $u^*\in L^2_{\mathcal F}(0,T;\mathbb R^d)$". In the substrate `Peng1990_SMP_Stochastic`, a solution of the SDE already requires its diffusion integrand $u^*$ to lie in $L^2_{\mathcal F}$ and $\sup_tE|X^*_t|^2<\infty$, so the claim "every solution has these properties" would be empty; it is stated as *existence* of a solution with continuous paths, $E\sup|X^*|^2<\infty$ and $u^*\in L^2$. Uniqueness of the closed-loop solution is not claimed by the proposition and is not stated.
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, p. 20, Proposition 5.3, (5.4) p. 15, (5.14) p. 20

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_MeanVariance_Model
import Definitions.Def_TimeInconsLQ_MeanVariance_Market

namespace TimeInconsLQ.MeanVariance

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

/-- Proposition 5.3 (p. 20). With `(M, U)` and `(Γ⁽²⁾, γ⁽²⁾)` as in Propositions 5.1–5.2, the
wealth equation (first equation of (5.4)) under the feedback (5.14), `u*_s = α_s X*_s + β_s`, has a
solution `X*` with almost surely continuous paths on `[0, T]` and `E sup_{t ≤ T} |X*_t|² < ∞`, and
`u* ∈ L²_𝓕(0, T; ℝᵈ)`. -/
theorem proposition_5_3 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (mk : Market Ω d)
    (hmk : mk.Standing)
    (M : ℝ≥0 → Ω → ℝ) (U : ℝ≥0 → Ω → Fin d → ℝ) (hMU : mk.Class58 M U)
    (Γ2 : ℝ≥0 → Ω → ℝ) (γ2 : ℝ≥0 → Ω → Fin d → ℝ) (hΓ : mk.Class513 M U Γ2 γ2) :
    ∃ X, mk.mvData.IsClosedLoop (mk.alpha M U) (mk.beta M γ2) X ∧
      (∀ᵐ ω ∂mk.P, ContinuousOn (fun s => X s ω 0) (Set.Iic mk.T)) ∧
      ∫⁻ ω, (⨆ s ≤ mk.T, ‖X s ω 0‖ₑ ^ 2) ∂mk.P < ⊤ ∧
      Peng1990.SMP.L2F mk.filt mk.P mk.T (mk.uStar M U γ2 X) := by sorry

end TimeInconsLQ.MeanVariance
