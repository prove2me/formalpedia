-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularInterpolationNodes_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalModularInterpolationNodes_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:52:41.338236+00:00
-- url     : https://prove2.me/theorems/a44c964b-3dbd-4e83-b521-c159b2fbd2c5
-- title:
--   Tanner Lifted Product: lps Original Modular Interpolation Nodes injective
-- statement:
--   The r+1 integer complex interpolation nodes are pairwise distinct.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L246-L251
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L246-L251

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalModularInterpolationNodes_injective (r : ℕ) :
    Function.Injective (fun i : Fin (r+1) => (i.val:ℂ)) := by sorry
