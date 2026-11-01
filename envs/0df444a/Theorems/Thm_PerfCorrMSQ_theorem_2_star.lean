-- Prove2me | Theorems.Thm_PerfCorrMSQ_theorem_2_star
-- name    : PerfCorrMSQ.theorem_2_star
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:42:02.441494+00:00
-- url     : https://prove2.me/theorems/e3876e87-74b4-4615-a81f-eaa8fb74001e
-- title:
--   Theorem 2* — under (Ia), $\hat X^n\Rightarrow\hat X_C$, the Erlang-C Halfin–Whitt diffusion
-- statement:
--   Consider the many-server queues $M/M_{pc}/n+M_{pc}$, $n\ge1$: Poisson arrivals at rate $\lambda_n>0$, $n$ servers, FIFO service, and for each customer a service requirement $S\sim\mathrm{Exp}(1)$ and a patience $T=S/\theta$ perfectly correlated with it ($\theta>0$); customers whose patience runs out before service abandon. All systems live on one probability space, with initial states independent of the fresh draws. Let $X^n(t)$ be the number of customers in system $n$ and $\hat X^n=n^{-1/2}(X^n-n)$.
--
--   Assume the square-root staffing rule (1.1), $\sqrt n(1-\lambda_n/n)\to\beta\in\mathbb R$, and the initial condition (Ia): $\hat X^n(0)\Rightarrow X_0$ with law $\nu$, and $\hat L^n(0)=n^{-1/2}L^n(0)\Rightarrow0$, where $L^n(0)$ is the total remaining phase-1 time of the customers in service plus the total elapsed waiting time of the customers in queue at time $0$. Then
--
--   $$
--   \hat X^n\Rightarrow\hat X_C\quad\text{in }D\text{ as }n\to\infty,
--   $$
--
--   where $\hat X_C$ is the (unique strong) solution of the Erlang-C Halfin–Whitt SDE (1.2) with $\mu=1$,
--
--   $$
--   d\hat X_C(t)=m_C(\hat X_C(t))\,dt+\sqrt2\,dB(t),\qquad\hat X_C(0)=X_0,\qquad m_C(x)=\begin{cases}-\beta,&x\ge0,\\-(\beta+x),&x<0,\end{cases}
--   $$
--
--   with $X_0\sim\nu$ independent of the standard Brownian motion $B$. The conclusion has two parts: a solution with initial law $\nu$ exists, and $\hat X^n$ converges in distribution to every such solution.
--
--   Although customers abandon, the limit is the Erlang-C diffusion, not the Erlang-A one. Theorem 2 (p.7) is the special case $L^n(0)=0$ (Assumption 1), under which (Ia) reduces to $\hat X^n(0)\Rightarrow X_0$.
--
--   **Formalization Note** The solution of (1.2) is `ErlangA.Diffusion.IsDiffusionSolution P' 1 β 0 ν b q`: its drift with Erlang-A abandonment rate $0$ is $m_C$. The model is `PerfCorrMSQ.IsModel`.
--
--   Differences from the source:
--   - reading: independence of the initial state from the arrivals and the fresh service/patience draws not stated → the initial state (Qⁿ(0), Zⁿ(0), ℓⁿ(0), rⁿ(0)) is independent of the fresh draws, which are mutually independent; the initial state's joint law is otherwise arbitrary; reason: the proofs use it (the time-0 σ-algebra Fⁿ₀ of the martingales, p.11; X₀ independent of B in (1.2)); an initial state that depends on future arrivals keeps X̂ⁿ(0) correlated with the arrival noise and admits no such theorem
--   - reading: §3.3 (p.9) is silent on the patience of the customers waiting at time 0 → an initial waiting customer has remaining patience Exp(θ), independent of everything else, and service requirement θ(ℓ + remaining patience); reason: memorylessness with perfect correlation T = S/θ, as in (2.1); it is the bound hⁿⱼ(t) ≤ θℓⁿᵢ(0) + θ(Tⁿ₀ ∧ t) of p.20 and the abandonment rate θ per waiting customer in (4.1)
--   - reading: (3.8) (p.9) calls rⁿⱼ(t) the "remaining service time" of a customer in phase 1 → rⁿⱼ(0) is the remaining phase-1 time, followed by an independent Exp(1) phase 2, and Lⁿ(0) sums the remaining phase-1 times; reason: §3.3 opens with "remaining phase-1 service time"; the equality on p.11 that counts the customers with rⁿⱼ(t) > 0 and the bound gⁿᵢ(t) ≤ rⁿᵢ(0) on p.20 use this meaning; Lⁿ(0) is then the smaller quantity, so (Ia) and (Ib) are the weaker hypotheses, and this is the stronger reading
--   - encoding: the M/M_pc/n + M_pc system described in words (§2, §3.3) → an explicit FIFO non-idling n-server recursion over customers indexed in queue order (initial waiting customers first, then arrivals); a customer is served iff its service can start strictly before its deadline; counts are Set.ncard; the initial waiting customers are in FIFO order, so their elapsed waits are nonincreasing along the queue; reason: the recursion is the verbal model; the tie rule and the junk value of an infinite count only matter on null events; the order is the page's "ith customer in the queue" under FIFO
--   - encoding: (Ia): (X̂ⁿ(0), L̂ⁿ(0)) ⇒ (X₀, 0) in ℝ² → the laws of X̂ⁿ(0) converge weakly to a probability measure ν, and L̂ⁿ(0) → 0 in probability; reason: the second limit is a constant, so joint convergence in ℝ² is equivalent to the two marginal statements
--   - encoding: sequences indexed by n ≥ 1 → sequences indexed by n : ℕ, model hypotheses for n ≥ 1; reason: at n = 0 every scaled process is the constant 0 (division by √0 = 0), and only the tail of a sequence matters for the limits
--   - reading: X̂ⁿ ⇒ X̂_C for X̂_C the unique strong solution of (1.2) → (i) a solution of (1.2) with initial law ν exists on some probability space, and (ii) X̂ⁿ converges in distribution to every solution with initial law ν; reason: the statement presupposes existence; a bare 'for every solution' would be vacuous if none existed; both parts together are the stronger reading
--   - encoding: (1.2) with µ = 1 and its unique strong solution → ErlangA.Diffusion.IsDiffusionSolution P' 1 β 0 ν b q: q(0) ∼ ν independent of the standard Brownian motion b, q adapted to σ(q(0)) ∨ σ(b), and q(t) = q(0) + ∫₀ᵗ m_C(q(s)) ds + √2 b(t) a.s.; every path of b and q is continuous on [0, ∞); reason: drift 1 β 0 is −(β + x) for x ≤ 0 and −β for x > 0, which is m_C (both give −β at 0); the third argument is the Erlang-A abandonment rate, 0 here; every solution has such a version, and convergence in distribution depends only on the law
--   - encoding: ⇒ in D → PuhaWardFluid.Limit.ConvInDist dist on paths t ↦ X̂ⁿ(t), t ≥ 0 (J₁, coupling form); limit objects range over probability spaces in the universe Type; reason: by the Skorokhod representation this is weak convergence in D; the limit is continuous; every law on path space is carried by such a space
-- source:
--   Yu and Perry, Many-Server Heavy-Traffic Limits for Queueing Systems with Perfectly Correlated Service and Patience Times, arXiv:2008.12890v1, Theorem 2*, p.10 (proof §5.1, p.13); Theorem 2, p.7; (1.1)–(1.2), p.3; (Ia), p.9

import Mathlib
import Definitions.Def_PerfCorrMSQ_Scaled
import Definitions.Def_PuhaWardFluid_Limit_Paths
import Definitions.Def_ErlangA_Diffusion_SDE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace PerfCorrMSQ

/-- **Theorem 2*** (Yu–Perry, arXiv:2008.12890v1, p.10): assume that (1.1) holds with `β ∈ ℝ`. If (Ia) holds,
then `X̂ⁿ ⇒ X̂_C` in `D` as `n → ∞`, where `X̂_C` is the solution of the Erlang-C Halfin–Whitt SDE
(1.2), `dX̂_C(t) = m_C(X̂_C(t)) dt + √2 dB(t)`, `X̂_C(0) = X₀ ∼ ν`, with `m_C(x) = −β` for `x ≥ 0`
and `m_C(x) = −(β + x)` for `x < 0` (`µ = 1`).

Theorem 2 (p.7) is the special case `Lⁿ(0) = 0` (Assumption 1), under which (Ia) reduces to
`X̂ⁿ(0) ⇒ X₀`.

**Formalization Note.** The model is `PerfCorrMSQ.IsModel` (`µ = 1`, `θ > 0`; readings R1, R2:
initial state independent of the fresh draws, Exp(`θ`) remaining patience for initial waiting
customers). The solution of (1.2) is `ErlangA.Diffusion.IsDiffusionSolution P' 1 β 0 ν b q`: its
drift `ErlangA.Diffusion.drift 1 β 0` is `m_C` (the third argument is the Erlang-A abandonment
rate, `0` here, not this paper's `θ`). Reading R3: the conclusion has two parts, (i) a solution
with initial law `ν` exists, and (ii) `X̂ⁿ` converges in distribution in `D` (`J₁`, coupling form,
`PuhaWardFluid.Limit.ConvInDist`) to every such solution, restricted to times `t ≥ 0`. -/
theorem theorem_2_star {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ β : ℝ) (lam : ℕ → ℝ)
    (sys : SystemData Ω) (ν : ProbabilityMeasure ℝ) (hθ : 0 < θ) (hmodel : IsModel P θ lam sys)
    (hstaff : StaffingRule lam β) (hIa : InitialIa P θ sys ν) :
    (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (b : ℝ≥0 → Ω' → ℝ)
        (q : Ω' → ℝ → ℝ), ErlangA.Diffusion.IsDiffusionSolution P' 1 β 0 (ν : Measure ℝ) b q) ∧
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (b : ℝ≥0 → Ω' → ℝ)
        (q : Ω' → ℝ → ℝ), ErlangA.Diffusion.IsDiffusionSolution P' 1 β 0 (ν : Measure ℝ) b q →
        PuhaWardFluid.Limit.ConvInDist dist P (fun n ω (t : ℝ≥0) => Xhat θ sys n ω t) P'
          (fun ω (t : ℝ≥0) => q ω t) := by sorry

end PerfCorrMSQ
