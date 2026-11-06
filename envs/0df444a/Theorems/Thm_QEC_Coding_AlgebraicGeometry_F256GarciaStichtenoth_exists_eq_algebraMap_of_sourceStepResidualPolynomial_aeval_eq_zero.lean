-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_exists_eq_algebraMap_of_sourceStepResidualPolynomial_aeval_eq_zero
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.exists_eq_algebraMap_of_sourceStepResidualPolynomial_aeval_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:56:21.60848+00:00
-- url     : https://prove2.me/theorems/02659b6a-6a8c-4548-822e-93952c13bd50
-- title:
--   F256 Garcia Stichtenoth: exists eq algebra Map of source Step Residual Polynomial aeval eq zero
-- statement:
--   Every root after scalar extension is the image of one of the sixteen
--   constructed constants.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitAlgebra.lean#L220-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitAlgebra.lean#L220-L230

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisBase
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisStep
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitAlgebra
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.exists_eq_algebraMap_of_sourceStepResidualPolynomial_aeval_eq_zero
    {E : Type*} [Field E] [Algebra F256 E]
    (a : GaloisBaseSplitPoint) (y : E)
    (hy : Polynomial.aeval y (sourceStepResidualPolynomial a) = 0) :
    ∃ b ∈ sourceStepArtinSchreierRoots a,
      y = algebraMap F256 E b := by sorry
