-- Prove2me | Theorems.Thm_ShortestPlanarDisjoint_Main_lemma_5_3
-- name    : ShortestPlanarDisjoint.Main.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:24.212841+00:00
-- url     : https://prove2.me/theorems/3c2cfa04-1f51-4ef9-a03a-44ebc00e7526
-- title:
--   Lemma 5.3 — Leading monomials
-- statement:
--   For every return-free noncrossing state D within the crossing budget, its actual glued-component signature has leading exponent q_s in lambda_s, o_e in u_e and one in t_i exactly for opening terminals. This exponent has coefficient one. Different states have different such leading monomials. In particular the signature is nonzero, including when components close after gluing. The monomial priority is seam variables first, then terminal and side variables in disk-boundary order.
--
--   Differences from the source:
--   - generalization: planar disk layouts with r=f−1 and reversed seam identifications → any disk layout and any fixed same-order or reversed identifications, including empty blocks or endpoints; reason: the rank-one and stack arguments use only noncrossing and no returns; every source planar layout and its full signature is included
--   - encoding: formal signatures and their seam-first lexicographic leading monomials → finite Laurent sums over ZMod 2, zero-based Fin terminal/seam labels, involutive-permutation matchings, explicit component traversals and a nonzero leading-exponent predicate; reason: negative powers are formal, traversal counts each component once, and the exact exponent vector and coefficient are retained; finite relabelling changes no endpoint or state, and the larger ambient Laurent ring adds no source instance restriction
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Lemma 5.3, p. 19 (PDF p. 21)

import Definitions.Def_ShortestPlanarDisjoint_Main_StateSignature
set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main
/-- The exact leading exponent (6), coefficient one and separation of states.
The conclusion is independent of whether a seam preserves boundary order. -/
theorem lemma_5_3 {k f r b : ℕ} (L : DiskLayout k f r) (hb : 1 ≤ b)
    (sameOrder : Fin r → Bool) :
    (∀ D : DiskState L b,
      IsLeadingExponent L (D.signature sameOrder) D.topExponent ∧
      (D.signature sameOrder).coeff D.topExponent = 1) ∧
    Function.Injective (fun D : DiskState L b => D.topExponent) := by sorry
end ShortestPlanarDisjoint.Main
