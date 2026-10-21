-- Prove2me | Theorems.Thm_StochLoadBal_Makespan_effSize_facts
-- name    : StochLoadBal.Makespan.effSize_facts
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:24.131077+00:00
-- url     : https://prove2.me/theorems/60b7e577-6da4-46a8-9d3b-c9265a132959
-- title:
--   Effective-size facts (proofs of Observation 2 and Lemma 6, p. 12) — 0 ≤ β_k(Y) ≤ 1 for Y ∈ [0,1], and β_k(Y) ≥ E[Y]
-- statement:
--   Let $k\ge1$ be an integer.
--
--   1. If $Y$ is a random variable with values in $[0,1]$, then
--   $$0\ \le\ \beta_k(Y)\ \le\ 1 .$$
--   2. If $Y$ is integrable and $\mathbb E\big[e^{(\log k)Y}\big]<\infty$, then
--   $$\mathbb E[Y]\ \le\ \beta_k(Y).$$
--
--   Part 1 applied to truncated parts gives $p_{\max}=\max_{i,j}p_{ij}\le1$ in Observation 2; part 2 (Jensen's inequality) gives $\mathbb E[T_i]\le b+1$ for the truncated load of each machine in the proof of Lemma 6.
--
--   **Formalization Note** The page calls Jensen's inequality "for concave functions"; the inequality used is Theorem 5 for the convex function $\exp$. For $k=1$, $\beta_1=\mathbb E$ and part 2 is an equality.
-- source:
--   Gupta, Kumar, Nagarajan & Shen, Stochastic Load Balancing on Unrelated Machines, arXiv:1904.07271v1, p. 12, proof of Observation 2 and proof of Lemma 6 (unnumbered)

import Mathlib
import Definitions.Def_StochLoadBal_Makespan_Model

namespace StochLoadBal.Makespan

open MeasureTheory ProbabilityTheory

/-- The two effective-size facts used in the proofs of Observation 2 and Lemma 6 (p. 12), for
`k ≥ 1`: (a) a random variable `Y` with values in `[0, 1]` has `0 ≤ β_k(Y) ≤ 1`;
(b) every integrable `Y` with `E[e^{(log k) Y}] < ∞` has `E[Y] ≤ β_k(Y)` (Jensen). -/
theorem effSize_facts {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (hk : 1 ≤ k) :
    (∀ Y : Ω → ℝ, Measurable Y → (∀ ω, 0 ≤ Y ω ∧ Y ω ≤ 1) →
      0 ≤ effSize P k Y ∧ effSize P k Y ≤ 1) ∧
    (∀ Y : Ω → ℝ, Measurable Y → Integrable Y P →
      Integrable (fun ω => Real.exp (Real.log k * Y ω)) P →
      ∫ ω, Y ω ∂P ≤ effSize P k Y) := by sorry

end StochLoadBal.Makespan
