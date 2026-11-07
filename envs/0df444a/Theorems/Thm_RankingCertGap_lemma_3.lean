-- Prove2me | Theorems.Thm_RankingCertGap_lemma_3
-- name    : RankingCertGap.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:52:49.637788+00:00
-- url     : https://prove2.me/theorems/18de0b48-c10a-4ede-bb93-3188c24f296f
-- title:
--   Lemma 3, p.17 — rooted order-state representation
-- statement:
--   Let $G$ have online degree at most two, and fix an arrival prefix of length $t\le|J|$. If an offline node $i$ is positive after the prefix, meaning $\Pr[\mathcal E_i]>0$, then it admits a rooted order state $(W_i,\prec_i;i)$ such that for all rank vectors in $[0,1]^I$ with distinct entries,
--
--   $$
--   \mathcal E_i=O(W_i,\prec_i).
--   $$
--
--   So at degree two, the event that a vertex is still unmatched is exactly a pattern of rank comparisons in which that vertex is the largest.
--
--   Differences from the source:
--   - encoding: each instance has an arbitrary online arrival order → $J=\mathrm{Fin}\,n$ listed in arrival order; reason: an arbitrary order is a relabelling of $J$; same instances
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), Lemma 3, p.17; App. E.1, pp.53–55

import Mathlib
import Definitions.Def_RankingCertGap_RankingRun
import Definitions.Def_RankingCertGap_Score
import Definitions.Def_RankingCertGap_OrderState

open MeasureTheory

namespace RankingCertGap

/-- **Lemma 3 (Rooted order-state representation).** Xu, arXiv:2610.17545 (held file sha256
75896dd9…), Lemma 3, p.17: "Fix an arrival prefix in an online-degree-two instance. Every positive
offline node `i` admits a rooted order state `(W_i, ≺_i; i)` such that, on the event of distinct
offline ranks, `E_i = O(W_i, ≺_i)`."

**Formalization Note.** The prefix has length `t ≤ n`, including `t = 0` and `t = n`. A node is
positive when `Pr[E_i] > 0`. The event equality is pointwise on rank vectors in `[0, 1]^I` with
distinct entries. -/
theorem lemma_3 {m n : ℕ} (G : Inst m n) (hG : G.IsOnlineDegLE 2) (t : ℕ) (ht : t ≤ n)
    (i : Fin m) (hi : 0 < (rankMeasure m).real (G.safeEvent t i)) :
    ∃ (W : Finset (Fin m)) (r : Fin m → Fin m → Prop), IsRootedOrderState W r i ∧
      ∀ Y : Fin m → ℝ, DistinctRanks Y → (G.safeAfter Y t i ↔ orderEvent W r Y) := by sorry

end RankingCertGap
