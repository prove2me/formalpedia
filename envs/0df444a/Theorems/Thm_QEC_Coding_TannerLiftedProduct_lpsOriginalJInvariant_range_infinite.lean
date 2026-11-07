-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_range_infinite
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_range_infinite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:35:59.422445+00:00
-- url     : https://prove2.me/theorems/ae8b64b4-5cd5-430f-b9da-7b09587c8e71
-- title:
--   Tanner Lifted Product: lps Original JInvariant range infinite
-- statement:
--   Actual connected upper-half-plane continuity and proved nonconstancy give an infinite original j image; used for polynomial evaluation injectivity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean#L104-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean#L104-L110

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Separation.Connected
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_range_infinite :
    (Set.range lpsOriginalJInvariant).Infinite := by sorry
