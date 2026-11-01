-- Prove2me | Theorems.Thm_PerfCorrMSQ_proposition_5_1
-- name    : PerfCorrMSQ.proposition_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:41:19.577798+00:00
-- url     : https://prove2.me/theorems/d7b8a8b5-2e81-417b-8eed-5509b0f6a9e3
-- title:
--   Proposition 5.1 — under (Ia), the residual terms vanish and $(\hat M^n_A,\hat M^n_S,\hat M^n_R)\Rightarrow(B_1,B_2,0)$
-- statement:
--   Throughout, $\mu=1$, $\theta>0$ is the patience rate, $\lambda_n>0$ is the arrival rate of system $n$, and the systems $n\ge1$ satisfy the model `PerfCorrMSQ.IsModel`: Poisson arrivals, service requirements $S\sim\mathrm{Exp}(1)$ with patience $T=S/\theta$, FIFO service by $n$ servers with abandonment from the queue, and an initial state independent of the fresh draws.
--
--   Assume the staffing rule (1.1) with $\beta\in\mathbb R$ and (Ia). With the diffusion scaling $\hat Y^n=n^{-1/2}Y^n$, as $n\to\infty$:
--
--   1. (a) $\big(\int_0^\cdot\hat Q^n_0(s)\,ds,\ \int_0^\cdot\hat Z^n_0(s)\,ds\big)\Rightarrow(0\eta,0\eta)$ in $D^2$;
--   2. (b) $\big(\int_0^\cdot\hat U^n_1(s)\,ds,\ \int_0^\cdot\hat U^n_2(s)\,ds,\ \hat V^n\big)\Rightarrow(0\eta,0\eta,0\eta)$ in $D^3$;
--   3. (c) $(\hat M^n_A,\hat M^n_S,\hat M^n_R)\Rightarrow(B_1,B_2,0\eta)$ in $D^3$, where $B_1$ and $B_2$ are two independent standard Brownian motions.
--
--   Part (c) is stated in two parts: such a pair exists on some probability space, and the convergence in distribution holds to every such pair.
--
--   Differences from the source:
--   - reading: independence of the initial state from the arrivals and the fresh service/patience draws not stated → the initial state (Qⁿ(0), Zⁿ(0), ℓⁿ(0), rⁿ(0)) is independent of the fresh draws, which are mutually independent; the initial state's joint law is otherwise arbitrary; reason: the proofs use it (the time-0 σ-algebra Fⁿ₀ of the martingales, p.11; X₀ independent of B in (1.2)); an initial state that depends on future arrivals keeps X̂ⁿ(0) correlated with the arrival noise and admits no such theorem
--   - reading: §3.3 (p.9) is silent on the patience of the customers waiting at time 0 → an initial waiting customer has remaining patience Exp(θ), independent of everything else, and service requirement θ(ℓ + remaining patience); reason: memorylessness with perfect correlation T = S/θ, as in (2.1); it is the bound hⁿⱼ(t) ≤ θℓⁿᵢ(0) + θ(Tⁿ₀ ∧ t) of p.20 and the abandonment rate θ per waiting customer in (4.1)
--   - reading: (3.8) (p.9) calls rⁿⱼ(t) the "remaining service time" of a customer in phase 1 → rⁿⱼ(0) is the remaining phase-1 time, followed by an independent Exp(1) phase 2, and Lⁿ(0) sums the remaining phase-1 times; reason: §3.3 opens with "remaining phase-1 service time"; the equality on p.11 that counts the customers with rⁿⱼ(t) > 0 and the bound gⁿᵢ(t) ≤ rⁿᵢ(0) on p.20 use this meaning; Lⁿ(0) is then the smaller quantity, so (Ia) and (Ib) are the weaker hypotheses, and this is the stronger reading
--   - encoding: the M/M_pc/n + M_pc system described in words (§2, §3.3) → an explicit FIFO non-idling n-server recursion over customers indexed in queue order (initial waiting customers first, then arrivals); a customer is served iff its service can start strictly before its deadline; counts are Set.ncard; the initial waiting customers are in FIFO order, so their elapsed waits are nonincreasing along the queue; reason: the recursion is the verbal model; the tie rule and the junk value of an infinite count only matter on null events; the order is the page's "ith customer in the queue" under FIFO
--   - encoding: (Ia): (X̂ⁿ(0), L̂ⁿ(0)) ⇒ (X₀, 0) in ℝ² → the laws of X̂ⁿ(0) converge weakly to a probability measure ν, and L̂ⁿ(0) → 0 in probability; reason: the second limit is a constant, so joint convergence in ℝ² is equivalent to the two marginal statements
--   - encoding: sequences indexed by n ≥ 1 → sequences indexed by n : ℕ, model hypotheses for n ≥ 1; reason: at n = 0 every scaled process is the constant 0 (division by √0 = 0), and only the tail of a sequence matters for the limits
--   - encoding: ⇒ 0η in Dᵏ → BellWilliams2001.ThresholdPolicy.UocInProb to the zero path: for every t ≥ 0, sup_{s≤t} of the ℓ¹ norm → 0 in probability; reason: the limit is deterministic and continuous, so weak convergence in Dᵏ (J₁) is equivalent to this; §1.2 (i) defines o_P this way
--   - reading: ⇒ (B₁, B₂, 0η) for two independent standard Brownian motions → (i) two independent standard Brownian motions exist on some probability space, and (ii) the convergence holds to every such pair; reason: the statement presupposes the limit exists; a bare 'for every pair' would be vacuous if none existed; both parts together are the stronger reading
--   - encoding: standard Brownian motion → ErlangA.Diffusion.IsStandardBM: Mathlib's IsBrownianReal with every path continuous and every coordinate measurable; reason: every Brownian motion has such a version, and convergence in distribution depends only on the law
--   - encoding: ⇒ in D³ to a random limit → PuhaWardFluid.Limit.ConvInDist dist on paths ℝ≥0 → (Fin 3 → ℝ): copies on one probability space converging a.s. in J₁ with one time change for all coordinates; limit objects range over probability spaces in the universe Type; reason: the limit has continuous paths; by the Skorokhod representation this is weak convergence in D³; every law on path space is carried by such a space
-- source:
--   Yu and Perry, Many-Server Heavy-Traffic Limits for Queueing Systems with Perfectly Correlated Service and Patience Times, arXiv:2008.12890v1, Proposition 5.1, p.13 (proof pp.31–32)

import Mathlib
import Definitions.Def_PerfCorrMSQ_Scaled
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_PuhaWardFluid_Limit_Paths
import Definitions.Def_ErlangA_Diffusion_SDE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace PerfCorrMSQ

/-- **Proposition 5.1** (Yu–Perry, arXiv:2008.12890v1, p.13): assume (Ia). Then as `n → ∞`,
(a) `(∫₀^· Q̂ⁿ₀(s) ds, ∫₀^· Ẑⁿ₀(s) ds) ⇒ (0η, 0η)` in `D²`;
(b) `(∫₀^· Ûⁿ₁(s) ds, ∫₀^· Ûⁿ₂(s) ds, V̂ⁿ) ⇒ (0η, 0η, 0η)` in `D³`;
(c) `(M̂ⁿ_A, M̂ⁿ_S, M̂ⁿ_R) ⇒ (B₁, B₂, 0η)` in `D³`, where `B₁` and `B₂` are two independent standard
Brownian motions.

**Formalization Note.** Hypotheses of §5.1 (p.13): the model with `µ = 1`, `θ > 0`, the
staffing rule (1.1) with any `β ∈ ℝ`, and (Ia). (a), (b) use `BellWilliams2001.ThresholdPolicy.UocInProb` to the zero path. (c) is
stated in two parts: two independent standard Brownian motions exist on some probability space,
and the convergence in distribution (`PuhaWardFluid.Limit.ConvInDist`, `J₁` on `D³`, coupling
form) holds to every such pair. Brownian motions are `ErlangA.Diffusion.IsStandardBM`. -/
theorem proposition_5_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ β : ℝ) (lam : ℕ → ℝ)
    (sys : SystemData Ω) (ν : ProbabilityMeasure ℝ) (hθ : 0 < θ) (hmodel : IsModel P θ lam sys)
    (hstaff : StaffingRule lam β) (hIa : InitialIa P θ sys ν) :
    BellWilliams2001.ThresholdPolicy.UocInProb P
        (fun n ω t => ![∫ s in (0 : ℝ)..t, Q0hat θ sys n ω s, ∫ s in (0 : ℝ)..t, Z0hat θ sys n ω s])
        (fun _ _ => 0) ∧
      BellWilliams2001.ThresholdPolicy.UocInProb P
        (fun n ω t => ![∫ s in (0 : ℝ)..t, U1hat θ sys n ω s,
          ∫ s in (0 : ℝ)..t, U2hat θ lam sys n ω s, Vhat θ lam sys n ω t])
        (fun _ _ => 0) ∧
      (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (B₁ B₂ : ℝ≥0 → Ω' → ℝ),
        IsProbabilityMeasure P' ∧ ErlangA.Diffusion.IsStandardBM P' B₁ ∧
          ErlangA.Diffusion.IsStandardBM P' B₂ ∧
          IndepFun (fun ω (t : ℝ≥0) => B₁ t ω) (fun ω (t : ℝ≥0) => B₂ t ω) P') ∧
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (B₁ B₂ : ℝ≥0 → Ω' → ℝ),
        IsProbabilityMeasure P' → ErlangA.Diffusion.IsStandardBM P' B₁ →
        ErlangA.Diffusion.IsStandardBM P' B₂ →
        IndepFun (fun ω (t : ℝ≥0) => B₁ t ω) (fun ω (t : ℝ≥0) => B₂ t ω) P' →
        PuhaWardFluid.Limit.ConvInDist dist P
          (fun n ω (t : ℝ≥0) => ![MAhat lam sys n ω t, MShat θ sys n ω t, MRhat θ sys n ω t]) P'
          (fun ω t => ![B₁ t ω, B₂ t ω, 0]) := by sorry

end PerfCorrMSQ
