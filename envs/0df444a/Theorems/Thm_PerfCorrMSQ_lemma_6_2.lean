-- Prove2me | Theorems.Thm_PerfCorrMSQ_lemma_6_2
-- name    : PerfCorrMSQ.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:41:25.047236+00:00
-- url     : https://prove2.me/theorems/20bcbe69-496b-45d1-bdf1-8b485d6f9fa5
-- title:
--   Lemma 6.2 — $\{\tilde w^n\}$ is stochastically bounded in $D$
-- statement:
--   Throughout, $\mu=1$, $\theta>0$ is the patience rate, $\lambda_n>0$ is the arrival rate of system $n$, and the systems $n\ge1$ satisfy the model `PerfCorrMSQ.IsModel`: Poisson arrivals, service requirements $S\sim\mathrm{Exp}(1)$ with patience $T=S/\theta$, FIFO service by $n$ servers with abandonment from the queue, and an initial state independent of the fresh draws. Assume the square-root staffing rule (1.1), $\beta_n=(n-\lambda_n)/\sqrt n\to\beta\in\mathbb R$, and the initial condition (Ib): $\tilde X^n(0)\Rightarrow X_0$ with $X_0\ge0$ a.s. and $\tilde L^n(0)=n^{-3/4}L^n(0)\Rightarrow0$.
--
--   Let $w^n(t)$ be the minimum of $t$ and the waiting time of the head-of-line customer at time $t$ ($0$ if the queue is empty), and $\tilde w^n(t)=n^{1/4}w^n(n^{1/4}t)$. Then $\{\tilde w^n\}$ is stochastically bounded in $D$: for every $T>0$, $\sup_{t\le T}|\tilde w^n(t)|$ is tight over $n\ge1$.
--
--   Differences from the source:
--   - reading: independence of the initial state from the arrivals and the fresh service/patience draws not stated → the initial state (Qⁿ(0), Zⁿ(0), ℓⁿ(0), rⁿ(0)) is independent of the fresh draws, which are mutually independent; the initial state's joint law is otherwise arbitrary; reason: the proofs use it (the time-0 σ-algebra Fⁿ₀ of the martingales, p.11; X₀ independent of B in (1.2)); an initial state that depends on future arrivals keeps X̂ⁿ(0) correlated with the arrival noise and admits no such theorem
--   - reading: §3.3 (p.9) is silent on the patience of the customers waiting at time 0 → an initial waiting customer has remaining patience Exp(θ), independent of everything else, and service requirement θ(ℓ + remaining patience); reason: memorylessness with perfect correlation T = S/θ, as in (2.1); it is the bound hⁿⱼ(t) ≤ θℓⁿᵢ(0) + θ(Tⁿ₀ ∧ t) of p.20 and the abandonment rate θ per waiting customer in (4.1)
--   - reading: (3.8) (p.9) calls rⁿⱼ(t) the "remaining service time" of a customer in phase 1 → rⁿⱼ(0) is the remaining phase-1 time, followed by an independent Exp(1) phase 2, and Lⁿ(0) sums the remaining phase-1 times; reason: §3.3 opens with "remaining phase-1 service time"; the equality on p.11 that counts the customers with rⁿⱼ(t) > 0 and the bound gⁿᵢ(t) ≤ rⁿᵢ(0) on p.20 use this meaning; Lⁿ(0) is then the smaller quantity, so (Ia) and (Ib) are the weaker hypotheses, and this is the stronger reading
--   - encoding: the M/M_pc/n + M_pc system described in words (§2, §3.3) → an explicit FIFO non-idling n-server recursion over customers indexed in queue order (initial waiting customers first, then arrivals); a customer is served iff its service can start strictly before its deadline; counts are Set.ncard; the initial waiting customers are in FIFO order, so their elapsed waits are nonincreasing along the queue; reason: the recursion is the verbal model; the tie rule and the junk value of an infinite count only matter on null events; the order is the page's "ith customer in the queue" under FIFO
--   - reading: §5.2 proves Theorem 4* (β ≤ 0) under the standing assumption (Ib) (p.14) → the staffing rule (1.1) with any β ∈ ℝ, and (Ib); reason: §6.3 (p.31) applies Propositions 5.2–5.4 and their lemmas under (Ia), which implies (Ib), for every β ∈ ℝ in the proof of Theorem 2*; the statement for every β is the one the paper uses; the proof of Lemma 6.1 (pp.37–38) bounds Q̃ⁿ with βₙ ∧ 0 and keeps β ∈ ℝ
--   - encoding: (Ib): (X̃ⁿ(0), L̃ⁿ(0)) ⇒ (X₀, 0) in ℝ² with X₀ ≥ 0 w.p.1 → the laws of X̃ⁿ(0) converge weakly to a probability measure ν with ν((−∞,0)) = 0, and L̃ⁿ(0) → 0 in probability; reason: the second limit is a constant, so joint convergence in ℝ² is equivalent to the two marginal statements
--   - encoding: sequences indexed by n ≥ 1 → sequences indexed by n : ℕ, model hypotheses for n ≥ 1; reason: at n = 0 every scaled process is the constant 0 (division by √0 = 0), and only the tail of a sequence matters for the limits
--   - encoding: stochastically bounded (in D), §1.2 (ii) → MartingaleHT.InfiniteServer.IsSBD: for every T > 0, sup_{t≤T}|Yⁿ(t)| is tight over n ≥ 1; reason: the paper's definition, tightness of ‖Yⁿ‖_t for every t
-- source:
--   Yu and Perry, Many-Server Heavy-Traffic Limits for Queueing Systems with Perfectly Correlated Service and Patience Times, arXiv:2008.12890v1, Lemma 6.2, p.22 (proof §8)

import Mathlib
import Definitions.Def_PerfCorrMSQ_Scaled
import Definitions.Def_MartingaleHT_InfiniteServer_Toolkit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace PerfCorrMSQ

/-- **Lemma 6.2** (Yu–Perry, arXiv:2008.12890v1, p.22): `{w̃ⁿ : n ∈ ℤ₊}` is stochastically bounded in `D`.

**Formalization Note.** Standing hypotheses of §5.2 (p.14, "Throughout, we assume that (Ib)
holds"): the model with `µ = 1`, `θ > 0`, the staffing rule (1.1) with any `β ∈ ℝ`, and (Ib).
"`⇒ 0η` in `Dᵏ`" is `BellWilliams2001.ThresholdPolicy.UocInProb` to the zero path (for every
`t ≥ 0`, `sup_{s ≤ t} ‖Yⁿ(s)‖ → 0` in probability, the norm on `ℝᵏ` being `ℓ¹`), which is
equivalent because the limit is deterministic and continuous. "Stochastically bounded in `D`" (§1.2 (ii), p.4) is `MartingaleHT.InfiniteServer.IsSBD`: for
every `T > 0`, `sup_{t ≤ T} |Yⁿ(t)|` is tight over `n ≥ 1`. -/
theorem lemma_6_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ β : ℝ) (lam : ℕ → ℝ)
    (sys : SystemData Ω) (ν : ProbabilityMeasure ℝ) (hθ : 0 < θ) (hmodel : IsModel P θ lam sys)
    (hstaff : StaffingRule lam β) (hIb : InitialIb P θ sys ν) :
    MartingaleHT.InfiniteServer.IsSBD P (fun n ω t (_ : Fin 1) => wtil θ sys n ω t) := by sorry

end PerfCorrMSQ
