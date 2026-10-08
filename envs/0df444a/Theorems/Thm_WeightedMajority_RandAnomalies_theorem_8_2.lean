-- Prove2me | Theorems.Thm_WeightedMajority_RandAnomalies_theorem_8_2
-- name    : WeightedMajority.RandAnomalies.theorem_8_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:07.918019+00:00
-- url     : https://prove2.me/theorems/f5d213b2-39a7-4e2f-aca2-ee8fbd1d5230
-- title:
--   Theorem 8.2 — with $\eta$ anomalies, $\mathrm{opt}_{\mathrm{RAND}}(F,\eta) \ge \tfrac12\,\mathrm{opt}(F,0) + \eta$
-- statement:
--   Let $F$ be a pool of $\{0,1\}$-valued functions on an arbitrary domain $X$, let $\eta \ge 0$ be an integer, let $\mathrm{opt}(F,0)$ be the optimal worst-case number of mistakes of a deterministic learner on sequences consistent with some member of $F$, and let $\mathrm{opt}_{\mathrm{RAND}}(F,\eta)$ be the optimal worst-case expected number of mistakes of a randomized learner on sequences with at most $\eta$ anomalies with respect to $F$.
--
--   **Theorem 8.2.** If $F$ contains at least two functions, then
--   $$\mathrm{opt}_{\mathrm{RAND}}(F,\eta) \ \ge\ \tfrac12\,\mathrm{opt}(F,0) + \eta .$$
--
--   Thus every randomized learner has worst-case expected mistakes at least $\tfrac12\mathrm{opt}(F,0)+\eta$ over sequences fixed in advance with at most $\eta$ anomalies. When $\mathrm{opt}(F,0) = \infty$, these expected mistake counts are unbounded. It is the randomized counterpart of Theorem 8.1 ($\mathrm{opt}(F,\eta) \ge \mathrm{opt}(F,0) + 2\eta$), and shows that the coefficient $1$ of $\eta$ in the expected mistake bound of the randomized Weighted Majority algorithm WMR cannot be improved by any randomized algorithm.
--
--   **Formalization Note** $\mathrm{opt}(F,0) \in \mathbb N\cup\{\infty\}$ is cast to $[0,\infty]$, where $\tfrac12\cdot\infty + \eta = \infty$. "$|F| > 1$" is `F.Nontrivial` (two distinct members), which also covers infinite pools.
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), p. 252, Theorem 8.2

import Definitions.Def_WeightedMajority_RandAnomalies_OptRand

open scoped ENNReal

namespace WeightedMajority.RandAnomalies

/-- **Theorem 8.2** (Littlestone–Warmuth 1994, p. 252). For all target classes `F` and all
`η ≥ 0`, if `|F| > 1` then `opt_RAND(F, η) ≥ ½ opt(F, 0) + η`. -/
theorem theorem_8_2 {X : Type*} (F : Set (X → Bool)) (hF : F.Nontrivial) (η : ℕ) :
    ((WeightedMajority.Anomalies.opt F 0 : ℕ∞) : ℝ≥0∞) / 2 + η ≤ optRand F η := by sorry

end WeightedMajority.RandAnomalies
