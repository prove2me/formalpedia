-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalComplexBaseChangedCharts_pullback
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalComplexBaseChangedCharts_pullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:59:33.994376+00:00
-- url     : https://prove2.me/theorems/07325e91-d570-4e96-841c-02c7d6541dba
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Complex Base Changed Charts pullback
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Complex Base Changed Charts pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationBaseChange.lean#L422-L445
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationBaseChange.lean#L422-L445

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_ChartBaseChange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationBaseChange
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QEC.Coding.AlgebraicGeometry.ChartBaseChange
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalComplexBaseChangedCharts_pullback (N : ℕ) (hN : 0 < N) :
    IsPullback (lpsOriginalIntegerNormalComplexBaseChangedOverlapMap N hN false)
      (lpsOriginalIntegerNormalComplexBaseChangedOverlapMap N hN true)
      ((lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).f false)
      ((lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).f true) := by sorry
