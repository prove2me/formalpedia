-- Prove2me | Theorems.Thm_PolyakJuditsky_Averaging_linearized_average_close
-- name    : PolyakJuditsky.Averaging.linearized_average_close
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T23:41:46.957985+00:00
-- url     : https://prove2.me/theorems/3b830eab-0ad3-4ae8-95fb-fd8afee94620
-- title:
--   Proof of Theorem 2, Part 4 — $\sqrt t(\bar\Delta^1_t-\bar\Delta_t)\to0$
-- statement:
--   Assume Assumptions 3.1–3.4 (in the form of the definition file), with $R$ continuous, and let $x_t$, $\bar x_t$ be the iterate and average of algorithm (7) from a nonrandom $x_0$, $\Delta_0=x_0-x^*$ and $\bar\Delta_t=\bar x_t-x^*$. Define the linearised process driven by the same noise,
--   $$\Delta^1_0=\Delta_0,\qquad\Delta^1_t=\Delta^1_{t-1}-\gamma_tG\Delta^1_{t-1}-\gamma_t\xi_t\ (t\ge1),\qquad\bar\Delta^1_t=\frac1t\sum_{i=0}^{t-1}\Delta^1_i,$$
--   and $\delta_t=\bar\Delta^1_t-\bar\Delta_t$. Then
--   $$\sqrt t\,\delta_t\to0\quad\text{almost surely}.$$
--
--   Since $\bar\Delta^1_t$ satisfies the hypotheses of Theorem 1(a) with $A=G$, this step transfers the asymptotic normality of the linear case to the nonlinear algorithm.
--
--   **Formalization Note** The paper prints $\Delta^1_t=\Delta^1_{t-1}-\gamma_tG\Delta^1_{t-1}+\gamma_t\xi_t$ with initial condition "$\Delta^0_1=\Delta_0$". The error of (7) is $\Delta_t=\Delta_{t-1}-\gamma_tR(x_{t-1})-\gamma_t\xi_t$, and Part 4 compares the two processes path by path, so the noise enters with $-\gamma_t\xi_t$ (with $+$ the two processes do not stay close) and the initial condition is $\Delta^1_0=\Delta_0$. The linearised process is algorithm (7) with $R(x)=Gx$ started at $\Delta_0$. "Almost surely" follows the Appendix's convention that all relations between random variables hold a.s. $R$ is assumed continuous. The paper states no regularity of $R$, but its proof needs $\nabla V(x-x^*)^TR(x)$ to be bounded away from $0$ on every annulus $\varepsilon\le|x-x^*|\le\rho$ (the constant $\alpha$ of (A13) on the ball $|\Delta|\le R$, and the step "almost sure convergence of the algorithm follows from Parts 1 and 2", pp. 849–850). Continuity together with Assumption 3.1 gives this; with $R$ only measurable, a root-free $R$ whose drift degenerates at one point off $x^*$ can trap the iterates there with positive probability.
-- source:
--   Polyak, Juditsky, Acceleration of stochastic approximation by averaging, SIAM J. Control Optim. 30 (1992), p. 850, proof of Theorem 2, Part 4

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model
import Definitions.Def_PolyakJuditsky_Averaging_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology

namespace PolyakJuditsky.Averaging

/-- Proof of Theorem 2, Part 4 (p. 850), sign-corrected: let `Δ¹` be the linearised process
`Δ¹_0 = Δ_0 = x_0 - x*`, `Δ¹_t = Δ¹_{t-1} - γ_t G Δ¹_{t-1} - γ_t ξ_t` (printed `+ γ_t ξ_t`), with
average `Δ̄¹_t`, and `Δ̄_t = x̄_t - x*`. Under Assumptions 3.1–3.4,
`δ_t = Δ̄¹_t - Δ̄_t` satisfies `√t δ_t → 0` almost surely.
`R` is assumed continuous (the paper states no regularity of `R`; its proof needs
`⟪∇V(x - x*), R x⟫` bounded away from `0` on every annulus `ε ≤ |x - x*| ≤ ρ`, p. 849–850,
which continuity and Assumption 3.1 give). -/
theorem linearized_average_close {N : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (x₀ xstar : EuclideanSpace ℝ (Fin N)) (γ : ℕ → ℝ)
    (R : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (ξ ξ0 : ℕ → Ω → EuclideanSpace ℝ (Fin N)) (V : EuclideanSpace ℝ (Fin N) → ℝ)
    (G S : Matrix (Fin N) (Fin N) ℝ) (lam : ℝ)
    (hR : Continuous R) (h31 : LyapunovAssumption R xstar V)
    (h32 : LinearizationAssumption R xstar G lam)
    (h33 : NoiseAssumption P ℱ x₀ γ R ξ ξ0 xstar S) (h34 : StepAssumption γ lam) :
    ∀ᵐ ω ∂P, Tendsto
      (fun t : ℕ => Real.sqrt t • (saAverage (x₀ - xstar) γ (matApply G) ξ t ω
        - (saAverage x₀ γ R ξ t ω - xstar))) atTop (𝓝 0) := by sorry

end PolyakJuditsky.Averaging
