-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_jacobiHalfTriangularDegree_neg_sub_one
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.jacobiHalfTriangularDegree_neg_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:24:08.207639+00:00
-- url     : https://prove2.me/theorems/4c14ff44-70d9-402b-8707-ab0256bffac3
-- title:
--   Jacobi Cube Product: jacobi Half Triangular Degree neg sub one
-- statement:
--   The Jacobi Cube Product construction uses the jacobi Half Triangular Degree neg sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L345-L351
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L345-L351

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
open QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
open JacobiGeneralCore.FormalPowerSeries
set_option linter.style.haveILetI false

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.jacobiHalfTriangularDegree_neg_sub_one (z : ℤ) :
    jacobiHalfTriangularDegree (-z - 1) =
      jacobiHalfTriangularDegree z := by sorry
