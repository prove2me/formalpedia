-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryCoordinate_adjoin_eq_top
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryCoordinate_adjoin_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:53:26.398128+00:00
-- url     : https://prove2.me/theorems/4fb384a8-ed8e-416a-bdbc-39f64f887763
-- title:
--   F256 Garcia Stichtenoth: step Auxiliary Coordinate adjoin eq top
-- statement:
--   The source auxiliary coordinate itself generates the degree-sixteen step
--   field over the preceding level.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/AuxiliaryMinpoly.lean#L92-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/AuxiliaryMinpoly.lean#L92-L117

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Galois
import Mathlib.FieldTheory.PrimitiveElement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AuxiliaryMinpoly
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K]
variable [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryCoordinate_adjoin_eq_top
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IntermediateField.adjoin K
        ({stepAuxiliaryCoordinate P x hx} : Set (StepField P x hx)) =
      (⊤ : IntermediateField K (StepField P x hx)) := by sorry
