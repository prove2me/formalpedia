-- Prove2me | Theorems.Thm_ShortestPlanarDisjoint_Main_lemma_5_8
-- name    : ShortestPlanarDisjoint.Main.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:32.634121+00:00
-- url     : https://prove2.me/theorems/aa6e936b-9dcd-4c54-8d2e-5ae7e1680b6e
-- title:
--   Lemma 5.8 — Exact vanishing criterion
-- statement:
--   For every state, not only a surviving one, the substituted signature is zero if and only if the state has a cap in an inactive block. Both directions are stated.
--
--   Differences from the source:
--   - generalization: planar disk layouts with r=f−1 and reversed seam identifications → any disk layout and any fixed same-order or reversed identifications, including empty blocks or endpoints; reason: the rank-one and stack arguments use only noncrossing and no returns; every source planar layout and its full signature is included
--   - encoding: formal signatures and their seam-first lexicographic leading monomials → finite Laurent sums over ZMod 2, zero-based Fin terminal/seam labels, involutive-permutation matchings, explicit component traversals and a nonzero leading-exponent predicate; reason: negative powers are formal, traversal counts each component once, and the exact exponent vector and coefficient are retained; finite relabelling changes no endpoint or state, and the larger ambient Laurent ring adds no source instance restriction
--   - encoding: substitution t_i=x_j in inactive blocks → identification with the block's first terminal variable; reason: this is an injective renaming of the independent x_j; it neither changes vanishing nor excludes a source state
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Lemma 5.8, p. 27 (PDF p. 29)

import Definitions.Def_ShortestPlanarDisjoint_Main_StateSignature
set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main
/-- Both directions of the exact vanishing criterion, for every state. -/
theorem lemma_5_8 {k f r b : ℕ} (L : DiskLayout k f r) (hb : 1 ≤ b)
    (sameOrder : Fin r → Bool) (active : Fin f → Bool) (D : DiskState L b) :
    substituteSignature L active (D.signature sameOrder) = 0 ↔
      ¬ D.Survives active := by sorry
end ShortestPlanarDisjoint.Main
