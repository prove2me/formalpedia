-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJHolomorphicEvalZ_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJHolomorphicEvalZ_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:22:15.785692+00:00
-- url     : https://prove2.me/theorems/3ef29153-c2f7-44b2-b3cd-6c07dd364ff8
-- title:
--   Tanner Lifted Product: lps Original JHolomorphic Eval Z injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original JHolomorphic Eval Z injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerAffineModel.lean#L127-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerAffineModel.lean#L127-L129

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Integral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJHolomorphicEvalZ_injective :
    Function.Injective lpsOriginalJHolomorphicEvalZ := by sorry
