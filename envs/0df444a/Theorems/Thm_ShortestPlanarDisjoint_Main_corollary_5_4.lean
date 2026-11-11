-- Prove2me | Theorems.Thm_ShortestPlanarDisjoint_Main_corollary_5_4
-- name    : ShortestPlanarDisjoint.Main.corollary_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:27.801898+00:00
-- url     : https://prove2.me/theorems/2b48e0a0-0224-4377-aec7-077931ce04b1
-- title:
--   Corollary 5.4 — Linear independence
-- statement:
--   Fix the disk layout, crossing budget and side identifications. The actual signatures of all states within the budget are linearly independent over F₂. This includes unrealized states; it is not independence of arbitrarily assigned polynomials.
--
--   Differences from the source:
--   - generalization: planar disk layouts with r=f−1 and reversed seam identifications → any disk layout and any fixed same-order or reversed identifications, including empty blocks or endpoints; reason: the rank-one and stack arguments use only noncrossing and no returns; every source planar layout and its full signature is included
--   - encoding: formal signatures and their seam-first lexicographic leading monomials → finite Laurent sums over ZMod 2, zero-based Fin terminal/seam labels, involutive-permutation matchings, explicit component traversals and a nonzero leading-exponent predicate; reason: negative powers are formal, traversal counts each component once, and the exact exponent vector and coefficient are retained; finite relabelling changes no endpoint or state, and the larger ambient Laurent ring adds no source instance restriction
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Corollary 5.4, p. 20 (PDF p. 22)

import Definitions.Def_ShortestPlanarDisjoint_Main_StateSignature
set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main
/-- Linear independence of the actual glued component signatures. -/
theorem corollary_5_4 {k f r b : ℕ} (L : DiskLayout k f r) (hb : 1 ≤ b)
    (sameOrder : Fin r → Bool) :
    LinearIndependent (ZMod 2) (fun D : DiskState L b => D.signature sameOrder) := by sorry
end ShortestPlanarDisjoint.Main
