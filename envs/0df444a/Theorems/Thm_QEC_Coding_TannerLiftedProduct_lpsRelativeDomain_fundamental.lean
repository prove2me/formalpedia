-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsRelativeDomain_fundamental
-- name    : QEC.Coding.TannerLiftedProduct.lpsRelativeDomain_fundamental
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:17:51.844866+00:00
-- url     : https://prove2.me/theorems/4b559bfe-4f72-4c44-8059-c2f700119f25
-- title:
--   Tanner Lifted Product: lps Relative Domain fundamental
-- statement:
--   The genuine inverse-section union is a subgroup fundamental domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRelativeCosetDomain.lean#L77-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRelativeCosetDomain.lean#L77-L85

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

theorem QEC.Coding.TannerLiftedProduct.lpsRelativeDomain_fundamental (H : Subgroup G) (s : Set α)
    (r : G ⧸ H → G)
    (hr : ∀c, QuotientGroup.mk (r c) = c) (hs : IsFundamentalDomain G s μ) :
    IsFundamentalDomain H (lpsRelativeDomain H s r) μ := by sorry
