-- Prove2me | Theorems.Thm_TopComponent
-- name    : TopComponent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:48:29.667422+00:00
-- url     : https://prove2.me/theorems/ba6b023a-61bf-42fd-9873-cc2caae75221
-- title:
--   Top Component: Top Component
-- statement:
--   The top-homogeneous-component reduction: if `EpAlg p P = 0` and
--   `P.totalDegree ≥ 2`, then `EpAlg p` already vanishes on the top homogeneous
--   component of `P`.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TopComponent.lean#L12-L173
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TopComponent.lean#L12-L173

module
public import Definitions.Def_PHarmonicPoly_EpAlgHomogeneous
public import Definitions.Def_PHarmonicPoly_TotalDegreePDeriv
public import Definitions.Def_PHarmonicPoly_TopComponent
public import Theorems.Thm_EpAlgHomogeneous
public import Theorems.Thm_TotalDegreePDeriv

set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial

theorem TopComponent {n : ℕ} (p : ℝ) {P : MvPolynomial (Fin n) ℝ}
    (hm : 2 ≤ P.totalDegree) (hE : EpAlg p P = 0) :
    EpAlg p (homogeneousComponent P.totalDegree P) = 0 := by sorry
