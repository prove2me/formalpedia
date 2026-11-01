-- Prove2me | Theorems.Thm_PerfCorrMSQ_proposition_5_2_a
-- name    : PerfCorrMSQ.proposition_5_2_a
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:41:13.810476+00:00
-- url     : https://prove2.me/theorems/a82d6590-5ab8-41b8-8fe2-a89f67210648
-- title:
--   Proposition 5.2(a) — the initial customers are negligible at LOF scale, and $T^n_0\Rightarrow0$ (corrected: $\tilde Q^n_0$ scales $Q^n_0$, not $Q^n$)
-- statement:
--   Throughout, $\mu=1$, $\theta>0$ is the patience rate, $\lambda_n>0$ is the arrival rate of system $n$, and the systems $n\ge1$ satisfy the model `PerfCorrMSQ.IsModel`: Poisson arrivals, service requirements $S\sim\mathrm{Exp}(1)$ with patience $T=S/\theta$, FIFO service by $n$ servers with abandonment from the queue, and an initial state independent of the fresh draws. Assume the square-root staffing rule (1.1), $\beta_n=(n-\lambda_n)/\sqrt n\to\beta\in\mathbb R$, and the initial condition (Ib): $\tilde X^n(0)\Rightarrow X_0$ with $X_0\ge0$ a.s. and $\tilde L^n(0)=n^{-3/4}L^n(0)\Rightarrow0$. LOF-scaled processes are $\tilde Y^n(t)=n^{-3/4}Y^n(n^{1/4}t)$ (centered at $n$ for $X$, $Z$, $Z_2$), $\tilde w^n(t)=n^{1/4}w^n(n^{1/4}t)$.
--
--   Then, as $n\to\infty$,
--
--   $$
--   n^{1/4}\Big(\int_0^\cdot\tilde Z^n_0(s)\,ds,\ \int_0^\cdot\tilde Q^n_0(s)\,ds\Big)\Rightarrow(0\eta,0\eta)\ \text{in }D^2,\qquad T^n_0\Rightarrow0\ \text{in }\mathbb R .
--   $$
--
--   Here $Z^n_0$ counts the initial customers in phase-1 service, $Q^n_0$ the initial waiting customers still waiting, and $T^n_0$ is the time the last initial waiting customer leaves the queue.
--
--   Differences from the source:
--   - reading: independence of the initial state from the arrivals and the fresh service/patience draws not stated → the initial state (Qⁿ(0), Zⁿ(0), ℓⁿ(0), rⁿ(0)) is independent of the fresh draws, which are mutually independent; the initial state's joint law is otherwise arbitrary; reason: the proofs use it (the time-0 σ-algebra Fⁿ₀ of the martingales, p.11; X₀ independent of B in (1.2)); an initial state that depends on future arrivals keeps X̂ⁿ(0) correlated with the arrival noise and admits no such theorem
--   - reading: §3.3 (p.9) is silent on the patience of the customers waiting at time 0 → an initial waiting customer has remaining patience Exp(θ), independent of everything else, and service requirement θ(ℓ + remaining patience); reason: memorylessness with perfect correlation T = S/θ, as in (2.1); it is the bound hⁿⱼ(t) ≤ θℓⁿᵢ(0) + θ(Tⁿ₀ ∧ t) of p.20 and the abandonment rate θ per waiting customer in (4.1)
--   - reading: (3.8) (p.9) calls rⁿⱼ(t) the "remaining service time" of a customer in phase 1 → rⁿⱼ(0) is the remaining phase-1 time, followed by an independent Exp(1) phase 2, and Lⁿ(0) sums the remaining phase-1 times; reason: §3.3 opens with "remaining phase-1 service time"; the equality on p.11 that counts the customers with rⁿⱼ(t) > 0 and the bound gⁿᵢ(t) ≤ rⁿᵢ(0) on p.20 use this meaning; Lⁿ(0) is then the smaller quantity, so (Ia) and (Ib) are the weaker hypotheses, and this is the stronger reading
--   - encoding: the M/M_pc/n + M_pc system described in words (§2, §3.3) → an explicit FIFO non-idling n-server recursion over customers indexed in queue order (initial waiting customers first, then arrivals); a customer is served iff its service can start strictly before its deadline; counts are Set.ncard; the initial waiting customers are in FIFO order, so their elapsed waits are nonincreasing along the queue; reason: the recursion is the verbal model; the tie rule and the junk value of an infinite count only matter on null events; the order is the page's "ith customer in the queue" under FIFO
--   - reading: §5.2 proves Theorem 4* (β ≤ 0) under the standing assumption (Ib) (p.14) → the staffing rule (1.1) with any β ∈ ℝ, and (Ib); reason: §6.3 (p.31) applies Propositions 5.2–5.4 and their lemmas under (Ia), which implies (Ib), for every β ∈ ℝ in the proof of Theorem 2*; the statement for every β is the one the paper uses; the proof of Lemma 6.1 (pp.37–38) bounds Q̃ⁿ with βₙ ∧ 0 and keeps β ∈ ℝ
--   - encoding: (Ib): (X̃ⁿ(0), L̃ⁿ(0)) ⇒ (X₀, 0) in ℝ² with X₀ ≥ 0 w.p.1 → the laws of X̃ⁿ(0) converge weakly to a probability measure ν with ν((−∞,0)) = 0, and L̃ⁿ(0) → 0 in probability; reason: the second limit is a constant, so joint convergence in ℝ² is equivalent to the two marginal statements
--   - encoding: sequences indexed by n ≥ 1 → sequences indexed by n : ℕ, model hypotheses for n ≥ 1; reason: at n = 0 every scaled process is the constant 0 (division by √0 = 0), and only the tail of a sequence matters for the limits
--   - encoding: ⇒ 0η in Dᵏ → BellWilliams2001.ThresholdPolicy.UocInProb to the zero path: for every t ≥ 0, sup_{s≤t} of the ℓ¹ norm → 0 in probability; reason: the limit is deterministic and continuous, so weak convergence in Dᵏ (J₁) is equivalent to this; §1.2 (i) defines o_P this way
--   - correction: the list on p.13 prints Q̃ⁿ₀(t) := n^{−3/4}Qⁿ(n^{1/4}t) → Q̃ⁿ₀(t) := n^{−3/4}Qⁿ₀(n^{1/4}t); reason: the printed definition makes the first clause false: take β = 0, Xⁿ(0) = n + ⌊n^{3/4}⌋ with everyone in phase 2 or waiting with no elapsed wait, so Lⁿ(0) = 0 and (Ib) holds with X₀ = 1; then Q̃ⁿ stays near x_F(t) > 0 (Theorem 4), so n^{1/4}∫₀¹Q̃ⁿ(s) ds → ∞; the proof on p.20 bounds ∫Qⁿ₀
-- source:
--   Yu and Perry, Many-Server Heavy-Traffic Limits for Queueing Systems with Perfectly Correlated Service and Patience Times, arXiv:2008.12890v1, Proposition 5.2(a), p.14 (proof pp.20–21)

import Mathlib
import Definitions.Def_PerfCorrMSQ_Scaled
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace PerfCorrMSQ

/-- **Proposition 5.2(a)** (Yu–Perry, arXiv:2008.12890v1, p.14): as `n → ∞`,
`n^{1/4}(∫₀^· Z̃ⁿ₀(s) ds, ∫₀^· Q̃ⁿ₀(s) ds) ⇒ (0η, 0η)` in `D²` and `Tⁿ₀ ⇒ 0` in `ℝ`.

**Formalization Note.** Standing hypotheses of §5.2 (p.14, "Throughout, we assume that (Ib)
holds"): the model with `µ = 1`, `θ > 0`, the staffing rule (1.1) with any `β ∈ ℝ`, and (Ib).
"`⇒ 0η` in `Dᵏ`" is `BellWilliams2001.ThresholdPolicy.UocInProb` to the zero path (for every
`t ≥ 0`, `sup_{s ≤ t} ‖Yⁿ(s)‖ → 0` in probability, the norm on `ℝᵏ` being `ℓ¹`), which is
equivalent because the limit is deterministic and continuous. "`⇒ 0` in `ℝ`" is convergence in probability.
(correction) The list on p.13 prints `Q̃ⁿ₀(t) := n^{−3/4} Qⁿ(n^{1/4} t)`, a typo for `Qⁿ₀`: `Q̃ⁿ₀` here is
`PerfCorrMSQ.Q0til`, which scales `Qⁿ₀`, as the proof on p.20 does. With the printed definition the first
clause is false: for `X₀ = 1`, `n^{1/4} ∫₀¹ Q̃ⁿ(s) ds → ∞`. -/
theorem proposition_5_2_a {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ β : ℝ) (lam : ℕ → ℝ)
    (sys : SystemData Ω) (ν : ProbabilityMeasure ℝ) (hθ : 0 < θ) (hmodel : IsModel P θ lam sys)
    (hstaff : StaffingRule lam β) (hIb : InitialIb P θ sys ν) :
    BellWilliams2001.ThresholdPolicy.UocInProb P
        (fun n ω t => ![(n : ℝ) ^ ((1 : ℝ) / 4) * ∫ s in (0 : ℝ)..t, Z0til θ sys n ω s,
          (n : ℝ) ^ ((1 : ℝ) / 4) * ∫ s in (0 : ℝ)..t, Q0til θ sys n ω s]) (fun _ _ => 0) ∧
      TendstoInMeasure P (fun n ω => (sys.prim n ω).T0 θ n) atTop (fun _ => 0) := by sorry

end PerfCorrMSQ
