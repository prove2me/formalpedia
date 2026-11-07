-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_jacobiHalfTriangularDegree_nat
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.jacobiHalfTriangularDegree_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:24:57.224097+00:00
-- url     : https://prove2.me/theorems/331145d4-4c22-4e79-86bd-5c60209cbd5f
-- title:
--   Jacobi Cube Product: jacobi Half Triangular Degree nat
-- statement:
--   The Jacobi Cube Product construction uses the jacobi Half Triangular Degree nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L604-L611
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L604-L611

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

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.jacobiHalfTriangularDegree_nat (t : ℕ) :
    jacobiHalfTriangularDegree (t : ℤ) = (t + 1).choose 2 := by sorry
