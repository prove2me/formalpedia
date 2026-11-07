-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsRelativeDomain_components
-- name    : QEC.Coding.TannerLiftedProduct.lpsRelativeDomain_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:11:57.389129+00:00
-- url     : https://prove2.me/theorems/873728b6-b989-4ec5-868d-54f1915d3a3b
-- title:
--   Tanner Lifted Product: lps Relative Domain components
-- statement:
--   Distinct coset components are almost disjoint in the original measure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRelativeCosetDomain.lean#L89-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRelativeCosetDomain.lean#L89-L100

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

theorem QEC.Coding.TannerLiftedProduct.lpsRelativeDomain_components (H : Subgroup G) (s : Set α)
    (r : G ⧸ H → G)
    (hr : ∀c, QuotientGroup.mk (r c) = c) (hs : IsFundamentalDomain G s μ) :
    Pairwise (fun c d => AEDisjoint μ ((r c)⁻¹ • s)
      ((r d)⁻¹ • s)) := by sorry
