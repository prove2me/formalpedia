-- Prove2me | Theorems.Thm_ShortestPlanarDisjoint_Main_lemma_5_7
-- name    : ShortestPlanarDisjoint.Main.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:29.560106+00:00
-- url     : https://prove2.me/theorems/0a10cdee-0ca7-48bf-92ca-aedde0d8043f
-- title:
--   Lemma 5.7 — Surviving signatures
-- statement:
--   After identifying inactive-block terminal variables, every state having no cap in those blocks has a nonzero signature, leading coefficient one and the substituted exponent vector of formula (14). Distinct surviving states have distinct leading monomials. Active terminal variables remain independent.
--
--   Differences from the source:
--   - generalization: planar disk layouts with r=f−1 and reversed seam identifications → any disk layout and any fixed same-order or reversed identifications, including empty blocks or endpoints; reason: the rank-one and stack arguments use only noncrossing and no returns; every source planar layout and its full signature is included
--   - encoding: formal signatures and their seam-first lexicographic leading monomials → finite Laurent sums over ZMod 2, zero-based Fin terminal/seam labels, involutive-permutation matchings, explicit component traversals and a nonzero leading-exponent predicate; reason: negative powers are formal, traversal counts each component once, and the exact exponent vector and coefficient are retained; finite relabelling changes no endpoint or state, and the larger ambient Laurent ring adds no source instance restriction
--   - encoding: a new variable x_j for each inactive block → the first terminal variable of that block serves as x_j and all identified exponents are added; reason: block variables remain independent from other blocks, seam variables and side variables; unused variables have exponent zero, so their names change no polynomial
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Lemma 5.7, p. 26 (PDF p. 28)

import Definitions.Def_ShortestPlanarDisjoint_Main_StateSignature
set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main
/-- Nonvanishing, leading coefficient one, and separation after block substitution. -/
theorem lemma_5_7 {k f r b : ℕ} (L : DiskLayout k f r) (hb : 1 ≤ b)
    (sameOrder : Fin r → Bool) (active : Fin f → Bool) :
    (∀ D : DiskState L b, D.Survives active →
      let p := substituteSignature L active (D.signature sameOrder)
      let a := substitutedExponent L active D.topExponent
      p ≠ 0 ∧ IsLeadingExponent L p a ∧ p.coeff a = 1) ∧
    Function.Injective (fun D : {D : DiskState L b // D.Survives active} =>
      substitutedExponent L active D.val.topExponent) := by sorry
end ShortestPlanarDisjoint.Main
