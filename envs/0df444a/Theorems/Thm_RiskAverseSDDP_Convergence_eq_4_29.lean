-- Prove2me | Theorems.Thm_RiskAverseSDDP_Convergence_eq_4_29
-- name    : RiskAverseSDDP.Convergence.eq_4_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:50:31.12769+00:00
-- url     : https://prove2.me/theorems/5b2b3ea6-1143-43a5-8859-e239f8cdfcb7
-- title:
--   (4.29), proof of Theorem 4.1, p. 13 — almost surely, (4.28) at $n$ implies that the gap also vanishes along the iterations outside $\mathcal S_n$
-- statement:
--   Consider Algorithm 1 for the problem (3.9) under the standing assumptions and Assumption (H2), run with fixed deterministic choice rules on random samples $\xi^k_t$ that satisfy Assumption (H3) on a probability space $(\Omega,\mathcal F,\mathbb P)$. Let $t\in\{2,\dots,T\}$ and let $n$ be a node of stage $t-1$. Then almost surely: if
--   $$
--   \lim_{k\to+\infty,\ k\in\mathcal S_n}\mathcal Q_t(x^k_{[n]})-\mathcal Q^k_t(x^k_{[n]})=0
--   $$
--   then also
--   $$
--   \lim_{k\to+\infty,\ k\notin\mathcal S_n}\mathcal Q_t(x^k_{[n]})-\mathcal Q^k_t(x^k_{[n]})=0.\tag{4.29}
--   $$
--
--   This is the probabilistic half of the induction step in the proof of Theorem 4.1: because the scenario through $n$ is sampled with positive probability, independently of the past, the iterations in $\mathcal S_n$ are frequent enough to control the error at all iterations.
--
--   **Formalization Note** The run at $\omega$ is the run produced by the fixed rules from the samples $\xi^k_t(\omega)$, so it depends on $\omega$ only through the samples of the current and earlier iterations. Limits are in $\mathbb R\cup\{\pm\infty\}$ along the filters `atTop ⊓ 𝓟 𝒮_n` and `atTop ⊓ 𝓟 {k ≥ 1 : k ∉ 𝒮_n}`; if the latter set is finite the conclusion is vacuous, as a limit along a finite set is. The proof in the paper uses the strong law of large numbers and Lemmas A.1 and A.3 of Girardeau–Leclère–Philpott.
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, pp. 13–14, (4.29) in the proof of Theorem 4.1

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model
import Definitions.Def_RiskAverseSDDP_Convergence_Run
import Definitions.Def_RiskAverseSDDP_Convergence_Sampling
open Filter Topology MeasureTheory ProbabilityTheory

namespace RiskAverseSDDP.Convergence

theorem eq_4_29 {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (ε : ℝ)
    (hS : D.Standing) (hH2 : D.H2 ε) (R : Rules n M) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℕ → Ω → ℕ → Fin M) (hH3 : D.H3 P ξ)
    (r : Ω → RunData n M) (hr : ∀ ω, D.IsRun R (fun k t => ξ k ω t) (r ω)) :
    ∀ s, s + 2 ≤ T → ∀ ν : Fin s → Fin M, ∀ᵐ ω ∂P,
      Tendsto (fun k => D.Q (s + 1) ((r ω).hist k s ν) - (r ω).Qm k (s + 1) ((r ω).hist k s ν))
        (atTop ⊓ 𝓟 (iterSet (fun k t => ξ k ω t) s ν)) (𝓝 0) →
      Tendsto (fun k => D.Q (s + 1) ((r ω).hist k s ν) - (r ω).Qm k (s + 1) ((r ω).hist k s ν))
        (atTop ⊓ 𝓟 {k | 1 ≤ k ∧ sampNode (fun k t => ξ k ω t) k s ≠ ν}) (𝓝 0) := by sorry

end RiskAverseSDDP.Convergence
