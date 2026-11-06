-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceCoordinateSequence_units
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceCoordinateSequence_units
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:32:39.210808+00:00
-- url     : https://prove2.me/theorems/434ae210-daf3-4c0f-9df7-e79b9bbb45e3
-- title:
--   F256 Garcia Stichtenoth: source Coordinate Sequence units
-- statement:
--   Unit propagation along a literal finite source coordinate sequence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceRegularCoordinates.lean#L52-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceRegularCoordinates.lean#L52-L60

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceCoordinates
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalTraceSeed
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRegularCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {E : Type*} [_root_.Field E] [Algebra F256 E]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceCoordinateSequence_units (Q : GlobalPlace F256 E) (x : ℕ → E) (m : ℕ)
    (hrec : ∀ i < m, x (i + 1) ^ 16 + x (i + 1) = sourceStepRhs (x i))
    (hseed : Q.valuation (x 0 ^ 16 + x 0) = 1) (i : ℕ) (hi : i ≤ m) :
    Q.valuation (x i) = 1 ∧ Q.valuation (x i ^ 15 + 1) = 1 := by sorry
