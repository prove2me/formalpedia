-- Prove2me | Theorems.Thm_PerfCorrMSQ_lemma_6_3
-- name    : PerfCorrMSQ.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:40:01.052432+00:00
-- url     : https://prove2.me/theorems/89f09d16-e5c4-43d6-b854-a2729edc53b2
-- title:
--   Lemma 6.3 — $F^n(\cdot,t)$ is a martingale and $e^{\theta t}\sup_{s\le t}|F^n(s,t)|$ a submartingale
-- statement:
--   Throughout, $\mu=1$, $\theta>0$ is the patience rate, $\lambda_n>0$ is the arrival rate of system $n$, and the systems $n\ge1$ satisfy the model `PerfCorrMSQ.IsModel`: Poisson arrivals, service requirements $S\sim\mathrm{Exp}(1)$ with patience $T=S/\theta$, FIFO service by $n$ servers with abandonment from the queue, and an initial state independent of the fresh draws.
--
--   Fix $n\ge1$ and let
--
--   $$
--   F^n(s,t)=\#\{k:E^n_k\le s,\ E^n_k+T^n_k>t\}+\theta^{-1}\lambda_n\big(e^{-\theta t}-e^{-\theta(t-s)}\big)\qquad(4.9),
--   $$
--
--   the number of arrivals by time $s$ whose patience outlasts $t$, compensated. Then:
--
--   1. for each $t>0$, $\{F^n(s,t):s\in[0,t]\}$ is a martingale with respect to its natural filtration;
--   2. $\{e^{\theta t}\sup_{s\in[0,t]}|F^n(s,t)|:t\ge0\}$ is a submartingale with respect to its natural filtration.
--
--   The lemma depends only on the arrival process and the arrivals' patience times.
--
--   Differences from the source:
--   - reading: independence of the initial state from the arrivals and the fresh service/patience draws not stated → the initial state (Qⁿ(0), Zⁿ(0), ℓⁿ(0), rⁿ(0)) is independent of the fresh draws, which are mutually independent; the initial state's joint law is otherwise arbitrary; reason: the proofs use it (the time-0 σ-algebra Fⁿ₀ of the martingales, p.11; X₀ independent of B in (1.2)); an initial state that depends on future arrivals keeps X̂ⁿ(0) correlated with the arrival noise and admits no such theorem
--   - reading: §3.3 (p.9) is silent on the patience of the customers waiting at time 0 → an initial waiting customer has remaining patience Exp(θ), independent of everything else, and service requirement θ(ℓ + remaining patience); reason: memorylessness with perfect correlation T = S/θ, as in (2.1); it is the bound hⁿⱼ(t) ≤ θℓⁿᵢ(0) + θ(Tⁿ₀ ∧ t) of p.20 and the abandonment rate θ per waiting customer in (4.1)
--   - encoding: the M/M_pc/n + M_pc system described in words (§2, §3.3) → an explicit FIFO non-idling n-server recursion over customers indexed in queue order (initial waiting customers first, then arrivals); a customer is served iff its service can start strictly before its deadline; counts are Set.ncard; the initial waiting customers are in FIFO order, so their elapsed waits are nonincreasing along the queue; reason: the recursion is the verbal model; the tie rule and the junk value of an infinite count only matter on null events; the order is the page's "ith customer in the queue" under FIFO
--   - encoding: the martingale {Fⁿ(s,t) : s ∈ [0,t]} → the process s ↦ Fⁿ(min(s,t), t) on s ∈ ℝ≥0, with its natural filtration; reason: on [0,t] it is the same process with the same filtration; after t it is constant
--   - encoding: augmented natural filtration → natural filtration σ(X_u : u ≤ s) without the null sets; reason: augmentation by null sets changes no conditional expectation up to a.e. equality
--   - encoding: sup_{s∈[0,t]}|Fⁿ(s,t)| → the real supremum ⨆ over s ∈ [0,t]; reason: Fⁿ(·,t) has finitely many jumps on [0,t] a.s., so the set is bounded and the real supremum is the true one except on a null event
-- source:
--   Yu and Perry, Many-Server Heavy-Traffic Limits for Queueing Systems with Perfectly Correlated Service and Patience Times, arXiv:2008.12890v1, Lemma 6.3, p.24 (proof §8)

import Mathlib
import Definitions.Def_PerfCorrMSQ_Model
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
import Definitions.Def_MartingaleHT_InfiniteServer_Toolkit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace PerfCorrMSQ

/-- **Lemma 6.3** (Yu–Perry, arXiv:2008.12890v1, p.24): for each `n ≥ 1` and each `t > 0`,
`{Fⁿ(s, t) : s ∈ [0, t]}` is a martingale, and `{e^{θt} sup_{s ∈ [0, t]} |Fⁿ(s, t)| : t ≥ 0}` is a
submartingale, both with respect to their (augmented) natural filtrations.

**Formalization Note.** The martingale `s ↦ Fⁿ(s, t)` on `[0, t]` is written on `ℝ≥0` as the
process stopped at `t`, `s ↦ Fⁿ(s ∧ t, t)`, which has the same natural filtration on `[0, t]`.
Martingales are `MartingaleHT.InfiniteServer.IsMartingaleWrt`, submartingales
`PerfCorrMSQ.IsSubmartingaleWrt`, and the filtration is `PerfCorrMSQ.natFiltr` (augmentation by
null sets changes no conditional expectation up to a.e. equality). The supremum is the real
supremum over `s ∈ [0, t]`; it is a junk `0` only on the null event that infinitely many
arrivals occur before `t`. Only the model hypotheses (`µ = 1`, `θ > 0`, `λₙ > 0`, the laws and
independence of the primitives) are assumed. -/
theorem lemma_6_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ : ℝ) (lam : ℕ → ℝ)
    (sys : SystemData Ω) (hθ : 0 < θ) (hmodel : IsModel P θ lam sys) (n : ℕ) (hn : 1 ≤ n) :
    (∀ t : ℝ≥0, 0 < t →
      MartingaleHT.InfiniteServer.IsMartingaleWrt
        (natFiltr (fun s ω => (sys.prim n ω).F θ (lam n) ((min s t : ℝ≥0) : ℝ) t)) P
        (fun s ω => (sys.prim n ω).F θ (lam n) ((min s t : ℝ≥0) : ℝ) t)) ∧
      IsSubmartingaleWrt
        (natFiltr (fun t ω => Real.exp (θ * t) *
          ⨆ s : Set.Icc (0 : ℝ) t, |(sys.prim n ω).F θ (lam n) s t|)) P
        (fun t ω => Real.exp (θ * t) *
          ⨆ s : Set.Icc (0 : ℝ) t, |(sys.prim n ω).F θ (lam n) s t|) := by sorry

end PerfCorrMSQ
