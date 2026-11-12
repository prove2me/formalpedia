-- Prove2me | Theorems.Thm_QuantumGroupCodes836_Addressability_weighted_encoding
-- name    : QuantumGroupCodes836.Addressability.weighted_encoding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T17:13:58.600725+00:00
-- url     : https://prove2.me/theorems/ccc272b8-1a79-45bf-85bb-e7c82d15330e
-- title:
--   Lemma 3.8 — weighted encoding (corrected: all m+1 factors; dual-distance hypothesis)
-- statement:
--   Under the corrected construction hypotheses, there is a canonical encoding $E:F^L\to C_1/C_0^\perp$, compatible with restrictions of actual words of $C$. For every $m+1$ punctured words $f^0,\ldots,f^m$, put $x^a=E^{-1}(\pi f^a)$. Then
--
--   $$\sum_{P\in J}u_P\prod_{a=0}^m f^a_P=\sum_{Q\in L}u_Q\prod_{a=0}^m x^a_Q.$$
--
--   All $m+1$ factors and logical images are included. Existence and the identity are conclusions, not supplied encoding assumptions.
--
--   Differences from the source:
--   - encoding: CSS codes and module-linear sections → actual normalized coset subspaces and equivariant linear sections of actual quotients; reason: these are equivalent finite-coordinate models, with computed logical dimension and quotient-weight distance
--   - correction: d(C^perp)>|G| → d(C^perp)>r|G|; reason: C2: three independent length-four repetition blocks with trivial G and two selected singleton orbits satisfy the printed assumptions but give logical dimension 1 instead of 2
--   - correction: Equation (8) displays only m factors despite quantifying m+1 words → Equation (8) uses all m+1 words and all their logical images; reason: C3: the F4 code and weights in MODERATION_NOTES.md satisfy all assumptions but the printed four-factor identity has left side 0 and right side x^4 nonzero
--   - generalization: there exists an encoding E → E is the canonical encoding E(c_L) = π(c_{L̄}) of diagram (9); reason: the proof on p.12 constructs exactly this E; the Lean conclusion implies the source one
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), Lemma 3.8, pp.11–12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Definitions.Def_QuantumGroupCodes836_Addressability_Construction

set_option autoImplicit false
open scoped Classical

namespace QuantumGroupCodes836.Addressability

theorem weighted_encoding {F G : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F] [Group G] [Fintype G]
    {n r m : ℕ} (C : Code F (Fin n)) (A : CodeAction F (Fin n) G C)
    (p : Fin r → Fin n) (u : Fin n → F) (h : ConstructionAssumptions C A p m u) :
    let L := chosenOrbits A p
    let Q := puncturedCSS C L
    ∃ E, canonicalEncodingOption C L = some E ∧ CanonicalEncoding C L E ∧
      ∀ f : Fin (m + 1) → Q.classical,
        (∑ j, u ((remainingIndex L).symm j) * ∏ a, (f a : Fin Q.n → F) j) =
        ∑ j : L, u j * ∏ a, E.symm (Q.quotientMap (f a)) j := by sorry

end QuantumGroupCodes836.Addressability
