-- Prove2me | Theorems.Thm_WatsonPseudodeterminism_MASeparation_ambient_balanced
-- name    : WatsonPseudodeterminism.MASeparation.ambient_balanced
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:31:47.404567+00:00
-- url     : https://prove2.me/theorems/37286afb-d37e-444e-b727-203cb89fd78f
-- title:
--   §2.2 — Ambient balance (corrected: n ≥ 2)
-- statement:
--   Let $n\ge2$, $m\le n$, and $h=100\lceil\log_2n\rceil$. The full rectangle $S^m$ is balanced: for every output string $z\in\{0,1\}^m$,
--
--   $$\frac{|S^m|}{1.01\,2^m}\le |S^m_z|\le1.01\frac{|S^m|}{2^m}.$$
--
--   Both sides of the factor-$1.01$ bound are included, as required by the paper's definition of balanced. The statement includes $m=0$, when there is one empty input pair and one empty output string. This balance fact supplies the uniform-slice estimates used in the preprocessing phase.
--
--   Differences from the source:
--   - correction: ambient balance is asserted without excluding n=1 → n ≥ 2; reason: n=1 gives h=0; at m=1 the true-output slice is empty while |S¹|/2=1/2, violating the lower factor bound; n=0 has no logarithmic source meaning
--   - reading: h = 100 log n → h = 100 * Nat.clog 2 n, with logarithms to base two; reason: block lengths are integral; rounding upward preserves the small-discrepancy regime specified in the brief
--   - encoding: rectangles and sets of pairwise disjoint subrectangles → finite pairs of sides and a Finset of such pairs, with disjoint Cartesian products; reason: the input spaces are finite; every rectangle is represented, including the empty rectangle
-- source:
--   Thomas Watson, STOC 2027 submission #13 (October 2026), §2.2, “S^m itself is balanced”, p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/13.pdf

import Definitions.Def_WatsonPseudodeterminism_MASeparation_Balance

namespace WatsonPseudodeterminism.MASeparation

/-- §2.2, p. 7 (corrected: n ≥ 2).
At n=1, h=0 and m=1, the gadget is constantly false, so the true slice is empty
although the target mean is 1/2. This is not balanced within factor 1.01. -/
theorem ambient_balanced (n m : ℕ) (hn : 2 ≤ n) (hm : m ≤ n) :
    Balanced (fullRectangle (gadgetLength n) m) := by sorry

end WatsonPseudodeterminism.MASeparation
