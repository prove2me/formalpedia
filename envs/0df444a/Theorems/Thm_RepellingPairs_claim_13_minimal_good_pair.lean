-- Prove2me | Theorems.Thm_RepellingPairs_claim_13_minimal_good_pair
-- name    : RepellingPairs.claim_13_minimal_good_pair
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:04:18.906916+00:00
-- url     : https://prove2.me/theorems/0bc8ce90-cd64-4e6b-9d6c-3bc75aca738c
-- title:
--   Claim 13 — at a minimal good pair the cut metric drops by at least 2
-- statement:
--   Let $C,C'$ be perfect matchings with $C\succ C'$, and let $x,y$ be a good pair whose $x$-$y$ segment not containing $C(x)$ has the minimum number of points among all good pairs. Then for any bar $\bar i$ between $x$ and $y$ on that segment and any bar $\bar j$ between $C(x)$ and $C'(x)$ on the segment not containing $x$,
--
--   $$
--   \mathrm{dist}_C(\bar i,\bar j)-\mathrm{dist}_{C'}(\bar i,\bar j)\ge2.
--   $$
--
--   The uncrossing at such a pair lowers exactly these distances, by 2.
--
--   Differences from the source:
--   - encoding: "Assume w.l.o.g. that x, C(x), C′(x) appear clockwise" → no orientation is fixed: bars are located by the segment that avoids a given point; reason: the statement then covers both orientations, which is what the proof of Lemma 11 uses
--   - reading: the x-y segment "contains the minimum number of points" → the count of points strictly inside the segment; reason: including the two endpoints would change every count by the same 2
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), Claim 13, p.12

import Mathlib
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_PerfectMatching
import Definitions.Def_RepellingPairs_IsGoodPair

set_option autoImplicit false

namespace RepellingPairs

/-- **Claim 13.** If perfect matchings satisfy `C ≻ C′` and the good pair `x, y` has the fewest points on the `x`-`y`
segment not containing `C(x)`, then `dist_C(ī, j̄) - dist_C′(ī, j̄) ≥ 2` for any `ī` between `x` and `y` and
`j̄` between `C(x)` and `C′(x)`. Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version of October 23, 2026),
Claim 13, p.12.

**Formalization Note.** Unoriented, so both of the page's "w.l.o.g." orientations are covered: `ī` is on the
segment avoiding `C(x)`, and `j̄` on the segment avoiding `x`. `ī = x̄` is included. -/
theorem claim_13_minimal_good_pair {n : ℕ} (C C' : PerfectMatching n)
    (h : Config.StrictlyDominates C.config C'.config) (x y : Fin n)
    (hgood : IsGoodPair C C' x y)
    (hmin : ∀ x₂ y₂, IsGoodPair C C' x₂ y₂ → segmentCount C x y ≤ segmentCount C x₂ y₂)
    (i j : Fin n) (hi : BarBetween x y (C.partner x) i)
    (hj : BarBetween (C.partner x) (C'.partner x) x j) :
    Config.dist C'.config i j + 2 ≤ Config.dist C.config i j := by sorry

end RepellingPairs
