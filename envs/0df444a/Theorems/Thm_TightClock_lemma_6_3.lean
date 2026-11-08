-- Prove2me | Theorems.Thm_TightClock_lemma_6_3
-- name    : TightClock.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:20:44.467633+00:00
-- url     : https://prove2.me/theorems/a8103f13-538b-4201-b5dc-3285d4fa0dd9
-- title:
--   Lemma 6.3 — what the optimum gets
-- statement:
--   For an integer $q\ge8$ and $L\ge1$, let $\varepsilon_L=4/\sqrt B+L\exp(-q^{2B})$. Over the random tree of Instance 11 and the values $X\sim D$, drawn independently,
--
--   $$\Pr\Big[\exists\text{ a leaf }S:\ \sum_{i\in S}X_i\ge LB\Big]\ge1-\varepsilon_L.$$
--
--   This is the lower bound on the first best: the optimum collects about one portion $B$ from each tier.
--
--   Differences from the source:
--   - encoding: the depth $L$ of the tree, with levels $r=1,\dots,L$ in Instance 11 → the hypothesis `1 ≤ L`; reason: at $L=0$ there are no bidders and $h=a^2B/L$ divides by zero; the page's construction has $L\ge1$
--   - encoding: probability over the tree and the values → `treeExpect` of `priorExpect` of an indicator; reason: both laws are finite, and the page makes them independent
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Lemma 6.3, §6.3, p.37 (PDF p.40)

import Mathlib
import Definitions.Def_TightClock_treeExpect
import Definitions.Def_TightClock_hardPrior
import Definitions.Def_TightClock_priorExpect
import Definitions.Def_TightClock_nodeSet
import Definitions.Def_TightClock_leafNode
import Definitions.Def_TightClock_epsL

set_option autoImplicit false

namespace TightClock

open Classical in
/-- Lemma 6.3 (What the optimum gets), p.37 (PDF 40), of Afshinmehr et al., manuscript (STOC 2027 submission): with
probability at least `1 − ε_L` over the tree and the values, some leaf contains bidders of total value at least `LB`. -/
theorem lemma_6_3 (q L : ℕ) (hq : 8 ≤ q) (hL : 1 ≤ L) :
    1 - epsL q L ≤
      treeExpect q L (fun T => priorExpect (hardPrior q L hq hL) (fun v =>
        if ∃ s : Path q L L, (L : ℝ) * (B L : ℝ) ≤ ∑ i ∈ nodeSet T (leafNode s), v i then 1 else 0)) := by sorry

end TightClock
