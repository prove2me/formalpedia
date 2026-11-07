-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsRelativeDomain_covers
-- name    : QEC.Coding.TannerLiftedProduct.lpsRelativeDomain_covers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:17:47.211278+00:00
-- url     : https://prove2.me/theorems/731c8706-0811-4488-8598-31b1d1c92b99
-- title:
--   Tanner Lifted Product: lps Relative Domain covers
-- statement:
--   The actual section law gives almost-everywhere subgroup orbit coverage.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRelativeCosetDomain.lean#L36-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRelativeCosetDomain.lean#L36-L50

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
omit [Countable G] [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ]

theorem QEC.Coding.TannerLiftedProduct.lpsRelativeDomain_covers (H : Subgroup G) (s : Set α)
    (r : G ⧸ H → G) (hr : ∀c, QuotientGroup.mk (r c) = c) (hs : IsFundamentalDomain G s μ) :
    ∀ᵐ τ ∂μ,∃h : H,h • τ ∈ lpsRelativeDomain H s r := by sorry
