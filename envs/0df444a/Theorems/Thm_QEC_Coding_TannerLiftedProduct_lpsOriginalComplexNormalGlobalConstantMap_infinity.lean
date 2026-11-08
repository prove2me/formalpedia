-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalGlobalConstantMap_infinity
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalGlobalConstantMap_infinity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:58:34.906096+00:00
-- url     : https://prove2.me/theorems/0d47a467-5249-4817-b0ed-f93c1bfba3a5
-- title:
--   Tanner Lifted Product: lps Original Complex Normal Global Constant Map infinity
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Complex Normal Global Constant Map infinity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialSheaf.lean#L57-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialSheaf.lean#L57-L77

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalGlobalConstantMap_infinity :
    lpsOriginalComplexNormalGlobalConstantMap N hpos ≫
      (lpsOriginalComplexNormalGluedChartMap N hpos true).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (lpsOriginalComplexNormalInfinityChart N hpos))).hom =
    CommRingCat.ofHom (lpsOriginalComplexInfinityConstantRingHom N hpos) := by sorry
