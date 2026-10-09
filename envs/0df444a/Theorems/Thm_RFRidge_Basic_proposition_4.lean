-- Prove2me | Theorems.Thm_RFRidge_Basic_proposition_4
-- name    : RFRidge.Basic.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:48:10.952531+00:00
-- url     : https://prove2.me/theorems/70a1ef2b-8315-4a99-9fce-b194e4b9f4d2
-- title:
--   Proposition 4 (Cordes inequality), p. 37 — ‖A^s B^s‖ ≤ ‖AB‖^s for positive A, B and 0 ≤ s ≤ 1
-- statement:
--   Let $A,B$ be bounded, self-adjoint, positive operators on a Hilbert space and $0\le s\le1$. Then
--   $$\|A^sB^s\|\le\|AB\|^s .$$
--
--   The Cordes inequality is the operator-theoretic tool behind the interpolation inequality of Proposition 9.
--
--   **Formalization Note** The paper's Hilbert spaces are real; the statement is posed on a complex Hilbert space because Mathlib's continuous functional calculus for operators, which defines $A^s$, exists only there. The real case follows by complexification, which preserves operator norms of real operators and the order. At $s=0$, $A^0=I$ for positive $A$. Separability, assumed in the section preamble of App. C, is not needed for the statement and is dropped.
-- source:
--   Rudi & Rosasco, arXiv:1602.04474v5, Proposition 4, p. 37 (App. C preamble)

import Mathlib

namespace RFRidge.Basic

/-- Proposition 4 (Cordes inequality), p. 37: for positive (self-adjoint) bounded operators `A, B` on a
Hilbert space and `0 ≤ s ≤ 1`, `‖A^s B^s‖ ≤ ‖A B‖^s`. Posed on a complex Hilbert space, where `A^s` is
the continuous functional calculus power `CFC.rpow`. -/
theorem proposition_4 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A B : E →L[ℂ] E) (hA : 0 ≤ A) (hB : 0 ≤ B) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖A ^ s * B ^ s‖ ≤ ‖A * B‖ ^ s := by sorry

end RFRidge.Basic
