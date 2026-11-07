-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsRelativeFundamental_subgroupOf
-- name    : QEC.Coding.TannerLiftedProduct.lpsRelativeFundamental_subgroupOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:05:23.661204+00:00
-- url     : https://prove2.me/theorems/f3c54e1e-72a2-4ce2-b8da-4ab212d3292d
-- title:
--   Tanner Lifted Product: lps Relative Fundamental subgroup Of
-- statement:
--   Transport a true relative-subgroup domain back to its actual original subgroup.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRelativeCosetDomain.lean#L184-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRelativeCosetDomain.lean#L184-L189

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

theorem QEC.Coding.TannerLiftedProduct.lpsRelativeFundamental_subgroupOf {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace α] (H K : Subgroup G) (h : H ≤ K) {μ : Measure α}
    {s : Set α} (hs : IsFundamentalDomain (H.subgroupOf K) s μ) :
    IsFundamentalDomain H s μ := by sorry
