-- Prove2me | Theorems.Thm_PrizeAlloc_Interval_lemma_2
-- name    : PrizeAlloc.Interval.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:34.470978+00:00
-- url     : https://prove2.me/theorems/7e3d6cdf-cbf4-4f0b-840a-9dfc2f678a98
-- title:
--   Lemma 2 — order preservation, endowment monotonicity and consistency imply anonymity
-- statement:
--   Let $U$ be a countable set of at least three potential competitors and $\varphi$ a prize allocation rule. If $\varphi$ satisfies order preservation, endowment monotonicity and consistency, then it satisfies anonymity: for any two competitions $(N, \mathcal R, E)$, $(N', \mathcal R', E)$ with $|N| = |N'|$ and any $i \in N$, $j \in N'$ with $\mathcal R(i) = \mathcal R'(j)$,
--   $$\varphi_i(N, \mathcal R, E) = \varphi_j(N', \mathcal R', E).$$
--
--   So in Theorem 1 the prize may depend only on the number of competitors, the position and the endowment, without assuming this.
--
--   **Formalization Note** The standing assumption of the paper (p. 8) that $U$ is countable with at least three elements is carried as `[Countable U]` and three distinct elements; the proof uses a competitor outside a given pair.
-- source:
--   Dietzenbacher and Kondratev, Fair and Consistent Prize Allocation in Competitions, arXiv:2008.08985v2, p. 11, Lemma 2 (proof pp. 24–27)

import Mathlib
import Definitions.Def_PrizeAlloc_Interval_Setting

namespace PrizeAlloc.Interval

theorem lemma_2 {U : Type*} [DecidableEq U] [Countable U] (hU : ∃ a b c : U, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (φ : List U → ℝ → U → ℝ) (hφ : IsPrizeRule φ)
    (hOP : OrderPreserving φ) (hEM : EndowmentMonotone φ) (hCons : Consistent φ) :
    Anonymous φ := by sorry

end PrizeAlloc.Interval
