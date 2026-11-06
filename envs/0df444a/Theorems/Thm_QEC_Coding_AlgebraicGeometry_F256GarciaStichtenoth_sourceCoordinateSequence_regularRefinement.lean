-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceCoordinateSequence_regularRefinement
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceCoordinateSequence_regularRefinement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:35:15.568778+00:00
-- url     : https://prove2.me/theorems/21e56e1b-27d4-4350-a9d0-dc5e3e3b46ce
-- title:
--   F256 Garcia Stichtenoth: source Coordinate Sequence regular Refinement
-- statement:
--   Direct regular adjunction of the entire literal source coordinate
--   sequence, over any already present initial field containing its w-parameter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularSourceRefinement.lean#L30-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularSourceRefinement.lean#L30-L53

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRegularCoordinates
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularSourceRefinement
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {E : Type*} [_root_.Field E] [Algebra F256 E]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceCoordinateSequence_regularRefinement
    (Q : GlobalPlace F256 E) (K : IntermediateField F256 E) (x : ℕ → E) (m : ℕ)
    (hrec : ∀ i < m, x (i + 1) ^ 16 + x (i + 1) = sourceStepRhs (x i))
    (hseed : x 0 ^ 16 + x 0 ∈ K)
    (hregular : ∀ i ≤ m, x i ∈ Q.valuationRing) :
    RegularRefinement Q K (K ⊔ coordinateWindow x 0 m) := by sorry
