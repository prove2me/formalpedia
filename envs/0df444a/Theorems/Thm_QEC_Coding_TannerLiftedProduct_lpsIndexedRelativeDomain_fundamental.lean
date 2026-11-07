-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIndexedRelativeDomain_fundamental
-- name    : QEC.Coding.TannerLiftedProduct.lpsIndexedRelativeDomain_fundamental
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:05:22.74177+00:00
-- url     : https://prove2.me/theorems/c7277061-b274-4ab4-abab-b8a61ef2c309
-- title:
--   Tanner Lifted Product: lps Indexed Relative Domain fundamental
-- statement:
--   A genuine indexed coset section constructs a subgroup fundamental domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRelativeCosetDomain.lean#L139-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRelativeCosetDomain.lean#L139-L152

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
variable {G α I : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [Countable G]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]
  [Fintype I] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [Fintype I]

theorem QEC.Coding.TannerLiftedProduct.lpsIndexedRelativeDomain_fundamental (H : Subgroup G) (s : Set α)
    (hs : IsFundamentalDomain G s μ) (e : I ≃ G ⧸ H) (r : I → G)
    (hr : ∀i,QuotientGroup.mk (r i)=e i) :
    IsFundamentalDomain H (⋃i,(r i)⁻¹ • s) μ := by sorry
