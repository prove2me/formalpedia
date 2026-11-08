-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalGlobalConstantMap_chart
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalGlobalConstantMap_chart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:59:04.518604+00:00
-- url     : https://prove2.me/theorems/1e45486c-f79a-4e13-b87d-b204e36ebe89
-- title:
--   Tanner Lifted Product: lps Original Complex Normal Global Constant Map chart
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Complex Normal Global Constant Map chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialSheaf.lean#L26-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialSheaf.lean#L26-L33

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialSheaf
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "X" => lpsOriginalComplexNormalGluedScheme N hpos

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalGlobalConstantMap_chart (b : Bool) :
    lpsOriginalComplexNormalGlobalConstantMap N hpos ≫
      (lpsOriginalComplexNormalGluedChartMap N hpos b).appTop =
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫
      (lpsOriginalComplexChartToSpecC N hpos b).appTop := by sorry
