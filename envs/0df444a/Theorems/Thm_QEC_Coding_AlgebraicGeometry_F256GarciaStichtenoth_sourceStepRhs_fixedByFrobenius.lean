-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepRhs_fixedByFrobenius
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepRhs_fixedByFrobenius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:03:37.4341+00:00
-- url     : https://prove2.me/theorems/6d9b3247-e432-43b4-af4c-6a85183c0808
-- title:
--   F256 Garcia Stichtenoth: source Step Rhs fixed By Frobenius
-- statement:
--   The source recursion right-hand side at a selected finite base point is
--   fixed by the sixteenth-power Frobenius.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitAlgebra.lean#L67-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitAlgebra.lean#L67-L72

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisBase
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisStep
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitAlgebra
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepRhs_fixedByFrobenius (a : GaloisBaseSplitPoint) :
    sourceStepRhs (a : F256) ^ 16 = sourceStepRhs (a : F256) := by sorry
