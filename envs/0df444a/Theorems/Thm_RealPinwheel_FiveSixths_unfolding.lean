-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_unfolding
-- name    : RealPinwheel.FiveSixths.unfolding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:35:54.924964+00:00
-- url     : https://prove2.me/theorems/0827771f-19b1-433a-bdef-a8263fbe30ab
-- title:
--   Lemma 9 — unfolding into any positive number of tasks
-- statement:
--   Let $A=(a_1,\ldots,a_n)$ be a schedulable real-period instance, choose task $j$, and let $q$ be any positive integer. Remove that task, introduce $q$ distinct tasks each of period $qa_j$, and reorder the resulting periods to obtain $U_q(A,j)$. Then
--
--   $$\operatorname{Schedulable}(A)\Longrightarrow\operatorname{Schedulable}(U_q(A,j)).$$
--
--   There are $n-1+q$ tasks after the operation, including the case $q=1$. This permits task replication while preserving the exact all-multiplicity real-period validity condition.
--
--   Differences from the source:
--   - encoding: positive days and task labels 1 through n → natural days starting at zero and task positions Fin n; reason: day t encodes source day t+1 and position i encodes source task i+1; all windows and distinct task identities are preserved
--   - encoding: replacing and reordering the task tuple → sorting a list of origin-tagged surviving tasks and q new positions, then indexing its entries; reason: the list has exactly n-1+q entries; tags distinguish repetitions and retain the permutation of labels
-- source:
--   Hiroshi Fujiwara, Grzegorz Gutowski, Katsuhisa Ouchi, Alexander Wolff, STOC 2027 submission #885 (October 2026), Lemma 9, printed p. 4 (PDF p. 5)

import Definitions.Def_RealPinwheel_FiveSixths_Transformations

namespace RealPinwheel.FiveSixths

/-- Lemma 9, printed p. 4 (PDF p. 5): every positive q, including q=1. -/
theorem unfolding {n : ℕ} (A : Instance n) (hA : Schedulable A.period)
    (j : Fin n) (q : ℕ) (hq : 0 < q) :
    Schedulable (unfoldedPeriods A.period j q) := by sorry

end RealPinwheel.FiveSixths
