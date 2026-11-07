-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsRelativeDomain_measure
-- name    : QEC.Coding.TannerLiftedProduct.lpsRelativeDomain_measure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:05:11.690876+00:00
-- url     : https://prove2.me/theorems/e5b46995-5bf0-4060-9943-a56313ce181a
-- title:
--   Tanner Lifted Product: lps Relative Domain measure
-- statement:
--   The actual finite-index cover has exact index times original domain measure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRelativeCosetDomain.lean#L120-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRelativeCosetDomain.lean#L120-L130

import Mathlib.MeasureTheory.Group.FundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open MeasureTheory Set Filter
open scoped Pointwise ENNReal
noncomputable section
variable {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [Countable G]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsRelativeDomain_countableQuotient

theorem QEC.Coding.TannerLiftedProduct.lpsRelativeDomain_measure (H : Subgroup G) (s : Set α)
    [H.FiniteIndex] (r : G ⧸ H → G)
    (hr : ∀c, QuotientGroup.mk (r c) = c) (hs : IsFundamentalDomain G s μ) :
    (μ : Measure α) (lpsRelativeDomain H s r) =
      (H.index : ℝ≥0∞) * μ s := by sorry
