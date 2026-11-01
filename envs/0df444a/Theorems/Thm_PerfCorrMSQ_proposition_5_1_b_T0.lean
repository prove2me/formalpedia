-- Prove2me | Theorems.Thm_PerfCorrMSQ_proposition_5_1_b_T0
-- name    : PerfCorrMSQ.proposition_5_1_b_T0
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:41:26.989253+00:00
-- url     : https://prove2.me/theorems/9e362af2-7056-4a0b-b8d0-c0f686ab804d
-- title:
--   Claim in the proof of Proposition 5.1(b) — under (Ia), $n^{1/4}T^n_0\Rightarrow0$
-- statement:
--   Throughout, $\mu=1$, $\theta>0$ is the patience rate, $\lambda_n>0$ is the arrival rate of system $n$, and the systems $n\ge1$ satisfy the model `PerfCorrMSQ.IsModel`: Poisson arrivals, service requirements $S\sim\mathrm{Exp}(1)$ with patience $T=S/\theta$, FIFO service by $n$ servers with abandonment from the queue, and an initial state independent of the fresh draws.
--
--   Assume the staffing rule (1.1) with $\beta\in\mathbb R$ and the initial condition (Ia): $\hat X^n(0)\Rightarrow X_0$ and $\hat L^n(0)=n^{-1/2}L^n(0)\Rightarrow0$. Let $T^n_0$ be the time at which the last customer of the initial queue leaves the queue ($0$ if there is none). Then
--
--   $$
--   n^{1/4}T^n_0\Rightarrow0\quad\text{in }\mathbb R\ \text{as }n\to\infty .
--   $$
--
--   Differences from the source:
--   - reading: independence of the initial state from the arrivals and the fresh service/patience draws not stated → the initial state (Qⁿ(0), Zⁿ(0), ℓⁿ(0), rⁿ(0)) is independent of the fresh draws, which are mutually independent; the initial state's joint law is otherwise arbitrary; reason: the proofs use it (the time-0 σ-algebra Fⁿ₀ of the martingales, p.11; X₀ independent of B in (1.2)); an initial state that depends on future arrivals keeps X̂ⁿ(0) correlated with the arrival noise and admits no such theorem
--   - reading: §3.3 (p.9) is silent on the patience of the customers waiting at time 0 → an initial waiting customer has remaining patience Exp(θ), independent of everything else, and service requirement θ(ℓ + remaining patience); reason: memorylessness with perfect correlation T = S/θ, as in (2.1); it is the bound hⁿⱼ(t) ≤ θℓⁿᵢ(0) + θ(Tⁿ₀ ∧ t) of p.20 and the abandonment rate θ per waiting customer in (4.1)
--   - reading: (3.8) (p.9) calls rⁿⱼ(t) the "remaining service time" of a customer in phase 1 → rⁿⱼ(0) is the remaining phase-1 time, followed by an independent Exp(1) phase 2, and Lⁿ(0) sums the remaining phase-1 times; reason: §3.3 opens with "remaining phase-1 service time"; the equality on p.11 that counts the customers with rⁿⱼ(t) > 0 and the bound gⁿᵢ(t) ≤ rⁿᵢ(0) on p.20 use this meaning; Lⁿ(0) is then the smaller quantity, so (Ia) and (Ib) are the weaker hypotheses, and this is the stronger reading
--   - encoding: the M/M_pc/n + M_pc system described in words (§2, §3.3) → an explicit FIFO non-idling n-server recursion over customers indexed in queue order (initial waiting customers first, then arrivals); a customer is served iff its service can start strictly before its deadline; counts are Set.ncard; the initial waiting customers are in FIFO order, so their elapsed waits are nonincreasing along the queue; reason: the recursion is the verbal model; the tie rule and the junk value of an infinite count only matter on null events; the order is the page's "ith customer in the queue" under FIFO
--   - encoding: (Ia): (X̂ⁿ(0), L̂ⁿ(0)) ⇒ (X₀, 0) in ℝ² → the laws of X̂ⁿ(0) converge weakly to a probability measure ν, and L̂ⁿ(0) → 0 in probability; reason: the second limit is a constant, so joint convergence in ℝ² is equivalent to the two marginal statements
--   - encoding: sequences indexed by n ≥ 1 → sequences indexed by n : ℕ, model hypotheses for n ≥ 1; reason: at n = 0 every scaled process is the constant 0 (division by √0 = 0), and only the tail of a sequence matters for the limits
-- source:
--   Yu and Perry, Many-Server Heavy-Traffic Limits for Queueing Systems with Perfectly Correlated Service and Patience Times, arXiv:2008.12890v1, proof of Proposition 5.1(b), p.31

import Mathlib
import Definitions.Def_PerfCorrMSQ_Scaled

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace PerfCorrMSQ

/-- **Claim in the proof of Proposition 5.1(b)** (Yu–Perry, arXiv:2008.12890v1, p.31): under (Ia),
`n^{1/4} Tⁿ₀ ⇒ 0` in `ℝ` as `n → ∞`.

**Formalization Note.** Hypotheses of §5.1 (p.13): the model with `µ = 1`, `θ > 0`, the
staffing rule (1.1) with any `β ∈ ℝ`, and (Ia). "`⇒ 0` in `ℝ`" is convergence in probability. -/
theorem proposition_5_1_b_T0 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ β : ℝ) (lam : ℕ → ℝ)
    (sys : SystemData Ω) (ν : ProbabilityMeasure ℝ) (hθ : 0 < θ) (hmodel : IsModel P θ lam sys)
    (hstaff : StaffingRule lam β) (hIa : InitialIa P θ sys ν) :
    TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ) ^ ((1 : ℝ) / 4) * (sys.prim n ω).T0 θ n) atTop (fun _ => 0) := by sorry

end PerfCorrMSQ
