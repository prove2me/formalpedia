-- Prove2me | Theorems.Thm_PolyakJuditsky_Averaging_iterate_tendsto_ae
-- name    : PolyakJuditsky.Averaging.iterate_tendsto_ae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T23:41:17.643983+00:00
-- url     : https://prove2.me/theorems/6b3d9083-416c-495b-b368-e96167422489
-- title:
--   Proof of Theorem 2 — the iterate $x_t$ of (7) converges to $x^*$ almost surely
-- statement:
--   Under Assumptions 3.1–3.4 (in the form of the definition file), with $R$ continuous, the iterate of algorithm (7),
--   $$x_t=x_{t-1}-\gamma_t\bigl(R(x_{t-1})+\xi_t\bigr),$$
--   started at a nonrandom $x_0$, satisfies
--   $$x_t\to x^*\quad\text{almost surely}.$$
--
--   This is the almost sure convergence of the un-averaged algorithm, established in the proof of Theorem 2 from Parts 1 and 2. The almost sure convergence of the average $\bar x_t$ in Theorem 2 follows from it by Cesàro's lemma.
--
--   **Formalization Note** The statement is the unnumbered sentence after (A14) on p. 850. The hypotheses are those of Theorem 2. $R$ is assumed continuous. The paper states no regularity of $R$, but its proof needs $\nabla V(x-x^*)^TR(x)$ to be bounded away from $0$ on every annulus $\varepsilon\le|x-x^*|\le\rho$ (the constant $\alpha$ of (A13) on the ball $|\Delta|\le R$, and the step "almost sure convergence of the algorithm follows from Parts 1 and 2", pp. 849–850). Continuity together with Assumption 3.1 gives this; with $R$ only measurable, a root-free $R$ whose drift degenerates at one point off $x^*$ can trap the iterates there with positive probability.
-- source:
--   Polyak, Juditsky, Acceleration of stochastic approximation by averaging, SIAM J. Control Optim. 30 (1992), p. 850, proof of Theorem 2 (sentence after Eq. (A14))

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model
import Definitions.Def_PolyakJuditsky_Averaging_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology

namespace PolyakJuditsky.Averaging

/-- Proof of Theorem 2, p. 850 ("almost sure convergence of the algorithm follows from Parts 1
and 2"): under Assumptions 3.1–3.4, the iterate `x_t` of Eq. (7) converges to `x*` almost
surely.
`R` is assumed continuous (the paper states no regularity of `R`; its proof needs
`⟪∇V(x - x*), R x⟫` bounded away from `0` on every annulus `ε ≤ |x - x*| ≤ ρ`, p. 849–850,
which continuity and Assumption 3.1 give). -/
theorem iterate_tendsto_ae {N : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (x₀ xstar : EuclideanSpace ℝ (Fin N)) (γ : ℕ → ℝ)
    (R : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (ξ ξ0 : ℕ → Ω → EuclideanSpace ℝ (Fin N)) (V : EuclideanSpace ℝ (Fin N) → ℝ)
    (G S : Matrix (Fin N) (Fin N) ℝ) (lam : ℝ)
    (hR : Continuous R) (h31 : LyapunovAssumption R xstar V)
    (h32 : LinearizationAssumption R xstar G lam)
    (h33 : NoiseAssumption P ℱ x₀ γ R ξ ξ0 xstar S) (h34 : StepAssumption γ lam) :
    ∀ᵐ ω ∂P, Tendsto (fun t => saIterate x₀ γ R ξ t ω) atTop (𝓝 xstar) := by sorry

end PolyakJuditsky.Averaging
