-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalOrder_value
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFieldLocalOrder_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:59:47.240567+00:00
-- url     : https://prove2.me/theorems/69ef3e9e-9e34-4186-9055-765465c58693
-- title:
--   Tanner Lifted Product: lps Original Field Local Order value
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Field Local Order value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLocalMeromorphicOrder.lean#L101-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLocalMeromorphicOrder.lean#L101-L108

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
set_option backward.isDefEq.respectTransparency false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFieldLocalOrder_value (hpos : 0 < N) (x : LPSOriginalFilledCurve N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    ∀ f : lpsOriginalGeneratedFunctionField N hpos,
      lpsOriginalFieldLocalOrder N hN hpos x f =
        meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x) (lpsOriginalFieldToLocal N hN hpos x f) := by sorry
