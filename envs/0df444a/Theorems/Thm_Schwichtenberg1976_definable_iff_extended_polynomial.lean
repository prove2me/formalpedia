-- Prove2me | Theorems.Thm_Schwichtenberg1976_definable_iff_extended_polynomial
-- name    : Schwichtenberg1976.definable_iff_extended_polynomial
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T01:54:49.945981+00:00
-- url     : https://prove2.me/theorems/d41263bd-5699-47e6-9aea-b2d2af7f2deb
-- title:
--   Schwichtenberg's Definability Theorem: λ-Definable Functions over `ν` are Exactly the Extended Polynomials
-- statement:
--   A `k`-ary numerical function `f : ℕ^k → ℕ` is λ-definable over the Church numeral type `ν = (0 → 0) → (0 → 0)` in the simply typed λ-calculus if and only if `f` is an extended polynomial (`IsExtendedPolyInd f`), and if and only if `f` is definable from polynomials by case distinction on the vanishing or non-vanishing of its arguments (`IsPiecewisePolynomial k f`).
-- source:
--   Helmut Schwichtenberg, 'Definierbare Funktionen im λ-Kalkül mit Typen', Archiv für mathematische Logik und Grundlagenforschung 17, 1975/1976, pp. 113-114 (doi:10.1007/BF02011242). pp. 113-114.

import Definitions.Def_Schwichtenberg1976_Lambda

namespace Schwichtenberg1976

/-- **Schwichtenberg's Definability Theorem** (pp. 113–114):
A `k`-ary numerical function `f : (Fin k → Nat) → Nat` is λ-definable over the Church
numeral type `ν = (0 → 0) → (0 → 0)` in the simply typed λ-calculus if and only if
`f` is an extended polynomial (`IsExtendedPolyInd f`), and if and only if `f` is definable
from polynomials by case distinction on the vanishing or non-vanishing of its arguments
(`IsPiecewisePolynomial k f`). -/
theorem definable_iff_extended_polynomial
    (k : Nat) (f : (Fin k → Nat) → Nat) :
    (IsPiecewisePolynomial k f ↔ IsExtendedPolyInd f) ∧
    (IsLambdaDefinable k f ↔ IsExtendedPolyInd f) ∧
    (IsLambdaDefinable k f ↔ IsPiecewisePolynomial k f) := by
  sorry

end Schwichtenberg1976
