-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepResidualPolynomial_eq_prod_roots
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepResidualPolynomial_eq_prod_roots
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:56:15.105698+00:00
-- url     : https://prove2.me/theorems/cc3c86ad-22fc-46b6-ba85-40837830fb86
-- title:
--   F256 Garcia Stichtenoth: source Step Residual Polynomial eq prod roots
-- statement:
--   Literal factorization into the sixteen distinct constant roots.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitAlgebra.lean#L209-L216
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitAlgebra.lean#L209-L216

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisBase
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisStep
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitAlgebra
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepResidualPolynomial_eq_prod_roots
    (a : GaloisBaseSplitPoint) :
    sourceStepResidualPolynomial a =
      ∏ b ∈ sourceStepArtinSchreierRoots a, (X - C b) := by sorry
