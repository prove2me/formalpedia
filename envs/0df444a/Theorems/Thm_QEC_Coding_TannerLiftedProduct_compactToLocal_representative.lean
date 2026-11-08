-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_compactToLocal_representative
-- name    : QEC.Coding.TannerLiftedProduct.compactToLocal_representative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:59:53.772872+00:00
-- url     : https://prove2.me/theorems/decd9102-2028-4e60-8af4-a08943ce1657
-- title:
--   Tanner Lifted Product: compact To Local representative
-- statement:
--   The Tanner Lifted Product construction uses the compact To Local representative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLocalMeromorphicOrder.lean#L80-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLocalMeromorphicOrder.lean#L80-L84

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGerms
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericCompactDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalMeromorphicOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalLocalChartGermTopology

theorem QEC.Coding.TannerLiftedProduct.compactToLocal_representative (x : LPSOriginalFilledCurve N)
    (F : LPSOriginalFilledMeromorphicFunctionRing N hN) :
    lpsOriginalCompactToLocal N hN x ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict F) =
      lpsOriginalRepresentativeToLocal N hN x F := by sorry
