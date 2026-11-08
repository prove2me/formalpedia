-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalGlobalConstantMap_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalGlobalConstantMap_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:57:42.841197+00:00
-- url     : https://prove2.me/theorems/6e03a1b2-58c1-4820-b68e-fbefe6ed2285
-- title:
--   Tanner Lifted Product: lps Original Complex Normal Global Constant Map zero
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Complex Normal Global Constant Map zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialSheaf.lean#L35-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialSheaf.lean#L35-L55

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalGlobalConstantMap_zero :
    lpsOriginalComplexNormalGlobalConstantMap N hpos ≫
      (lpsOriginalComplexNormalGluedChartMap N hpos false).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (lpsOriginalComplexNormalZeroChart N hpos))).hom =
    CommRingCat.ofHom (lpsOriginalComplexZeroConstantRingHom N hpos) := by sorry
