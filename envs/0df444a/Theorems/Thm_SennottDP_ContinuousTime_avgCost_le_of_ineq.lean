-- Prove2me | Theorems.Thm_SennottDP_ContinuousTime_avgCost_le_of_ineq
-- name    : SennottDP.ContinuousTime.avgCost_le_of_ineq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T11:06:14.316351+00:00
-- url     : https://prove2.me/theorems/b8041415-4233-4cc9-ac1b-395017bb49ed
-- title:
--   Lemma 10.3.1 — a solution of the CTMDC average cost inequality bounds a stationary policy's average cost
-- statement:
--   Let $\Psi$ be a CTMDC satisfying Assumption (CTB) and let $e$ be a stationary policy for $\Psi$. Suppose there are a finite constant $Z$ and a real function $z$ on $S$ that is bounded below such that, for every $i\in S$, the series $\sum_j P_{ij}(e)z(j)$ converges and
--
--   $$Z\tau(i,e)+z(i)\ \ge\ G(i,e)+g(i,e)\tau(i,e)+\sum_j P_{ij}(e)z(j).$$
--
--   Then the average cost of $e$ satisfies $J^\Psi_e(i)\le Z$ for every $i\in S$.
--
--   This is the continuous time analogue of Lemma 7.2.1: a supersolution of the average cost optimality inequality, weighted by the expected sojourn times, bounds the ratio of expected cost to expected time.
--
--   **Formalization Note** $J^\Psi_e(i)\in[0,\infty]$ is compared with the real number $Z$ in `EReal`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 244, Lemma 10.3.1, eq. (10.15)

import Mathlib
import Definitions.Def_SennottDP_ContinuousTime_CTMDC

open scoped ENNReal

namespace SennottDP.ContinuousTime

/-- Lemma 10.3.1 (p. 244). -/
theorem avgCost_le_of_ineq {S Act : Type} [Countable S] (Ψ : CTMDC S Act) (hΨ : Ψ.IsValid)
    (tau B : ℝ) (hCTB : Ψ.CTB tau B) (e : S → Act) (he : ∀ i, e i ∈ Ψ.A i)
    (Z : ℝ) (z : S → ℝ) (hz : BddBelow (Set.range z)) (h1015 : Ψ.Ineq1015 e Z z) :
    ∀ i, ((Ψ.avgCost (Ψ.ofStationary e he) i : ℝ≥0∞) : EReal) ≤ (Z : EReal) := by sorry

end SennottDP.ContinuousTime
