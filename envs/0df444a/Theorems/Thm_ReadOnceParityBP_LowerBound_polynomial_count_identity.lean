-- Prove2me | Theorems.Thm_ReadOnceParityBP_LowerBound_polynomial_count_identity
-- name    : ReadOnceParityBP.LowerBound.polynomial_count_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:27:49.971712+00:00
-- url     : https://prove2.me/theorems/52619918-75c5-4e52-b7e4-ba08ddaf3195
-- title:
--   Definition 2.3 and §3 — multilinearity and parity identity
-- statement:
--   Let F be any field and n an even cycle length. The polynomial f of Definition 2.3 is multilinear in all 2n variables. For any two n-bit vectors x,y, its Boolean evaluation over F₂ satisfies
--
--   $$f_{\rm bool}(x,y)=\bigl(\#\{B:|B|=n/2,\ B\text{ is x-valid and y-eligible}\}\bmod 2\bigr).$$
--
--   Both assertions are retained together as the semantic bridge from the formal polynomial to exact counting. Multilinearity here concerns the formal monomials, not merely Boolean functional equality.
--
--   Differences from the source:
--   - encoding: cycle positions Zₙ and two n-variable blocks → Fin n for the positions and Fin n ⊕ Fin n for the variables; reason: this retains exactly 2n distinct variables and the ordinary representative order for positive even n
--   - generalization: positive even cycle lengths → also the empty cycle n=0; reason: the unique half-subset is empty; its empty matching makes the geometric clauses vacuous and its polynomial and exact count equal one
-- source:
--   Ben Lee Volk, STOC 2027 submission #132 (October 2026), Definition 2.3 p.4 and unnumbered Boolean-count observation §3 p.6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/132.pdf

import Mathlib
import Definitions.Def_ReadOnceParityBP_LowerBound_CanonicalMatching

set_option autoImplicit false

namespace ReadOnceParityBP.LowerBound

/-- Definition 2.3 and §3 p.6: multilinearity in all 2n variables and exact
agreement of Boolean evaluation with the parity of the semantic count. -/
theorem polynomial_count_identity (F : Type) [Field F] (n : ℕ) (hn : Even n) :
    IsMultilinear (rsyPoly F n) ∧
      ∀ x y : Fin n → Bool,
        fBool n (Sum.elim x y) = decide (Odd (validEligibleCount n x y)) := by sorry

end ReadOnceParityBP.LowerBound
