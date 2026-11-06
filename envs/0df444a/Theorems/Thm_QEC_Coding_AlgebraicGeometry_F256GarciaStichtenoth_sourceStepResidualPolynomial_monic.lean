-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepResidualPolynomial_monic
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepResidualPolynomial_monic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:55:42.190306+00:00
-- url     : https://prove2.me/theorems/55eaa00f-bb3a-4ee2-90a7-69356a63be1f
-- title:
--   F256 Garcia Stichtenoth: source Step Residual Polynomial monic
-- statement:
--   The F256 Garcia Stichtenoth construction uses the source Step Residual Polynomial monic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitAlgebra.lean#L153-L166
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitAlgebra.lean#L153-L166

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisBase
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisStep
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitAlgebra
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepResidualPolynomial_monic (a : GaloisBaseSplitPoint) :
    (sourceStepResidualPolynomial a).Monic := by sorry
