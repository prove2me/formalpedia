-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsRelativeDomain_aedisjoint
-- name    : QEC.Coding.TannerLiftedProduct.lpsRelativeDomain_aedisjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:17:46.442934+00:00
-- url     : https://prove2.me/theorems/54101eba-8216-4afe-9751-169bd5772414
-- title:
--   Tanner Lifted Product: lps Relative Domain aedisjoint
-- statement:
--   True section laws give almost-disjoint subgroup translates of the union.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRelativeCosetDomain.lean#L54-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRelativeCosetDomain.lean#L54-L74

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
omit [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ]

theorem QEC.Coding.TannerLiftedProduct.lpsRelativeDomain_aedisjoint (H : Subgroup G) (s : Set α)
    (r : G ⧸ H → G)
    (hr : ∀c, QuotientGroup.mk (r c) = c) (hs : IsFundamentalDomain G s μ) (h : H) (hh : h ≠ 1) :
    AEDisjoint μ (h • lpsRelativeDomain H s r) (lpsRelativeDomain H s r) := by sorry
