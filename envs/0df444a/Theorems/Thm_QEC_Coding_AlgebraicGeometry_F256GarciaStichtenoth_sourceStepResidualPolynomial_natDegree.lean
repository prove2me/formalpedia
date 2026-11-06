-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepResidualPolynomial_natDegree
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepResidualPolynomial_natDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:55:24.248235+00:00
-- url     : https://prove2.me/theorems/052450db-d83a-456d-bcda-72fa0a457918
-- title:
--   F256 Garcia Stichtenoth: source Step Residual Polynomial nat Degree
-- statement:
--   The F256 Garcia Stichtenoth construction uses the source Step Residual Polynomial nat Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitAlgebra.lean#L169-L183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitAlgebra.lean#L169-L183

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisBase
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisStep
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitAlgebra
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepResidualPolynomial_natDegree (a : GaloisBaseSplitPoint) :
    (sourceStepResidualPolynomial a).natDegree = 16 := by sorry
