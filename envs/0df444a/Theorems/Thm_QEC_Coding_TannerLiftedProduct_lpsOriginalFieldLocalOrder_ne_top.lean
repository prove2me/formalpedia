-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalOrder_ne_top
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFieldLocalOrder_ne_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:02:48.492334+00:00
-- url     : https://prove2.me/theorems/2b9ebc0d-9947-4fb4-b05a-5709ec36d6a1
-- title:
--   Tanner Lifted Product: lps Original Field Local Order ne top
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Field Local Order ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLocalMeromorphicOrder.lean#L111-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLocalMeromorphicOrder.lean#L111-L121

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFieldLocalOrder_ne_top (hpos : 0 < N) (x : LPSOriginalFilledCurve N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    ∀ f : lpsOriginalGeneratedFunctionField N hpos, f ≠ 0 →
      lpsOriginalFieldLocalOrder N hN hpos x f ≠ ⊤ := by sorry
