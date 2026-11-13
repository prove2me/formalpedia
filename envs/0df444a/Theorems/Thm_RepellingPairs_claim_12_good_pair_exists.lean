-- Prove2me | Theorems.Thm_RepellingPairs_claim_12_good_pair_exists
-- name    : RepellingPairs.claim_12_good_pair_exists
-- status  : Proved
-- author  : @iris
-- created : 2026-11-07T11:04:19.724682+00:00
-- url     : https://prove2.me/theorems/bdb5bdb8-f9ab-4f9c-9f3e-8b044068ad79
-- title:
--   Claim 12 — a good pair exists
-- statement:
--   Let $C,C'$ be perfect matchings on $n$ points of a circle with $C\succ C'$. Then there is a good pair $x,y$: an ordered pair of points such that the chords $(x,C(x))$ and $(y,C(y))$ cross, $y$ and $C'(x)$ lie on different sides of $(x,C(x))$, and $C(y)\in S(x)$ or $C'(y)\in S(x)$, where $S(x)$ is the boundary segment from $C(x)$ to $C'(x)$ that does not contain $x$.
--
--   Good pairs are where an uncrossing that preserves dominance is found.
--
--   Differences from the source:
--   - reading: S(x), the boundary segment from C(x) to C′(x) that does not contain x → the closed segment, endpoints included; reason: the case C(y) = C′(x) occurs, and the claim's proof treats it as in the segment
--   - encoding: n even → no parity hypothesis; reason: a fixed-point-free involution exists only for even n
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), Claim 12, p.11

import Mathlib
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_PerfectMatching
import Definitions.Def_RepellingPairs_IsGoodPair

set_option autoImplicit false

namespace RepellingPairs

/-- **Claim 12.** If perfect matchings satisfy `C ≻ C′`, there is at least one good pair. Chen, Pylyavskyy, Tan,
arXiv:2607.02883 (version of October 23, 2026), Claim 12, p.11. -/
theorem claim_12_good_pair_exists {n : ℕ} (C C' : PerfectMatching n)
    (h : Config.StrictlyDominates C.config C'.config) :
    ∃ x y, IsGoodPair C C' x y := by sorry

end RepellingPairs
