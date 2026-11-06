-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_irreducible
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_irreducible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:01:47.459028+00:00
-- url     : https://prove2.me/theorems/53450416-cb28-455f-8324-66b70562ecb2
-- title:
--   F256 Garcia Stichtenoth: step Auxiliary Polynomial irreducible
-- statement:
--   The F256 Garcia Stichtenoth construction uses the step Auxiliary Polynomial irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/AuxiliaryMinpoly.lean#L142-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/AuxiliaryMinpoly.lean#L142-L146

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Galois
import Mathlib.FieldTheory.PrimitiveElement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AuxiliaryMinpoly
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K]
variable [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_irreducible
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Irreducible (stepAuxiliaryPolynomial x) := by sorry
