-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepResidualPolynomial_splits
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepResidualPolynomial_splits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:56:13.18264+00:00
-- url     : https://prove2.me/theorems/a907ff1d-1fb9-47c3-9b58-df0b9fedf133
-- title:
--   F256 Garcia Stichtenoth: source Step Residual Polynomial splits
-- statement:
--   The selected source-step residual polynomial splits over `F256`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitAlgebra.lean#L201-L206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitAlgebra.lean#L201-L206

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisBase
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisStep
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitAlgebra
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepResidualPolynomial_splits (a : GaloisBaseSplitPoint) :
    (sourceStepResidualPolynomial a).Splits := by sorry
