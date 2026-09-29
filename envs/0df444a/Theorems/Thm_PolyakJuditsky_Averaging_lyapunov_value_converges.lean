-- Prove2me | Theorems.Thm_PolyakJuditsky_Averaging_lyapunov_value_converges
-- name    : PolyakJuditsky.Averaging.lyapunov_value_converges
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:40:43.294712+00:00
-- url     : https://prove2.me/theorems/a741af57-0be1-483e-925c-43bb07d37208
-- title:
--   Proof of Theorem 2, Part 1 — $V(\Delta_t)$ converges almost surely
-- statement:
--   Assume Assumptions 3.1–3.4 (in the form of the definition file) for the map $R$, its root $x^*$, the Lyapunov function $V$, the matrices $G$, $S$, the exponent $\lambda$, the steps $\gamma_t$ and the noise $\xi_t=\xi_t(0)+\zeta_t$, and let $R$ be continuous. Let $x_t$ be the iterate of algorithm (7) from a nonrandom $x_0$ and $\Delta_t=x_t-x^*$. Then almost surely there is a finite $V(\omega)$ with
--   $$V(\Delta_t)\to V(\omega)\qquad(t\to\infty).$$
--
--   This is the first step of the proof of Theorem 2. Together with $V(x)\ge\alpha|x|^2$ it shows that the iterates stay bounded almost surely.
--
--   **Formalization Note** "$V(\omega)$ is bounded" is read as: the limit is a finite real number for almost every $\omega$. The hypotheses are those of Theorem 2, with the corrections listed in the definition file. $R$ is assumed continuous. The paper states no regularity of $R$, but its proof needs $\nabla V(x-x^*)^TR(x)$ to be bounded away from $0$ on every annulus $\varepsilon\le|x-x^*|\le\rho$ (the constant $\alpha$ of (A13) on the ball $|\Delta|\le R$, and the step "almost sure convergence of the algorithm follows from Parts 1 and 2", pp. 849–850). Continuity together with Assumption 3.1 gives this; with $R$ only measurable, a root-free $R$ whose drift degenerates at one point off $x^*$ can trap the iterates there with positive probability.
-- source:
--   Polyak, Juditsky, Acceleration of stochastic approximation by averaging, SIAM J. Control Optim. 30 (1992), p. 849, proof of Theorem 2, Part 1

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model
import Definitions.Def_PolyakJuditsky_Averaging_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology

namespace PolyakJuditsky.Averaging

/-- Proof of Theorem 2, Part 1 (p. 849): under Assumptions 3.1–3.4, with `Δ_t = x_t - x*` the
error of the iterate of Eq. (7), `V(Δ_t)` converges almost surely to a finite limit.
`R` is assumed continuous (the paper states no regularity of `R`; its proof needs
`⟪∇V(x - x*), R x⟫` bounded away from `0` on every annulus `ε ≤ |x - x*| ≤ ρ`, p. 849–850,
which continuity and Assumption 3.1 give). -/
theorem lyapunov_value_converges {N : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (x₀ xstar : EuclideanSpace ℝ (Fin N)) (γ : ℕ → ℝ)
    (R : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (ξ ξ0 : ℕ → Ω → EuclideanSpace ℝ (Fin N)) (V : EuclideanSpace ℝ (Fin N) → ℝ)
    (G S : Matrix (Fin N) (Fin N) ℝ) (lam : ℝ)
    (hR : Continuous R) (h31 : LyapunovAssumption R xstar V)
    (h32 : LinearizationAssumption R xstar G lam)
    (h33 : NoiseAssumption P ℱ x₀ γ R ξ ξ0 xstar S) (h34 : StepAssumption γ lam) :
    ∀ᵐ ω ∂P, ∃ c : ℝ, Tendsto (fun t => V (saIterate x₀ γ R ξ t ω - xstar)) atTop (𝓝 c) := by sorry

end PolyakJuditsky.Averaging
