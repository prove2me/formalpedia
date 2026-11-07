-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaDilatedForm_nonzero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaDilatedForm_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:35:49.084946+00:00
-- url     : https://prove2.me/theorems/fbe851e4-777b-4518-8f56-bf512761e2c6
-- title:
--   Tanner Lifted Product: lps Original Delta Dilated Form nonzero
-- statement:
--   Positive N and actual nowhere-zero Delta prove the original dilated form is a nonzero FUNCTION; used by genuine norm nonvanishing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean#L171-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean#L171-L179

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaDilatedForm_nonzero (N : ℕ) (hN : 0<N) :
    (lpsOriginalDeltaDilatedForm N hN:ℍ→ℂ)≠0 := by sorry
