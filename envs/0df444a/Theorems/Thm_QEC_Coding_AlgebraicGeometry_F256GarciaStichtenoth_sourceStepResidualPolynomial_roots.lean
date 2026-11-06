-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepResidualPolynomial_roots
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepResidualPolynomial_roots
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:55:48.412847+00:00
-- url     : https://prove2.me/theorems/57a7fa71-9596-45d9-8641-b8ff42572310
-- title:
--   F256 Garcia Stichtenoth: source Step Residual Polynomial roots
-- statement:
--   The residual polynomial roots are precisely the constructed constant
--   fibre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitAlgebra.lean#L187-L198
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitAlgebra.lean#L187-L198

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisBase
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisStep
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitAlgebra
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepResidualPolynomial_roots (a : GaloisBaseSplitPoint) :
    (sourceStepResidualPolynomial a).roots =
      (sourceStepArtinSchreierRoots a : Finset F256).val := by sorry
