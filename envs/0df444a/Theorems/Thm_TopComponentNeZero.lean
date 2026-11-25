-- Prove2me | Theorems.Thm_TopComponentNeZero
-- name    : TopComponentNeZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:35:12.34274+00:00
-- url     : https://prove2.me/theorems/be0c5e2c-712d-4b9e-95d7-ee59fa74b6f3
-- title:
--   Top Component Ne Zero: Top Component Ne Zero
-- statement:
--   The top homogeneous component of a nonzero polynomial is nonzero. Mathlib
--   has only the vanishing of components ABOVE the total degree.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TopComponentNeZero.lean#L10-L24
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TopComponentNeZero.lean#L10-L24

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_TopComponentNeZero
set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial

theorem TopComponentNeZero {σ R : Type*} [CommSemiring R]
    {P : MvPolynomial σ R} (hP : P ≠ 0) :
    homogeneousComponent P.totalDegree P ≠ 0 := by sorry
