-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIndexedRelativeDomain_integral
-- name    : QEC.Coding.TannerLiftedProduct.lpsIndexedRelativeDomain_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:05:29.299293+00:00
-- url     : https://prove2.me/theorems/1ed30579-f121-4fff-9317-8ab4a37936d8
-- title:
--   Tanner Lifted Product: lps Indexed Relative Domain integral
-- statement:
--   The integrable indexed cover equals its true finite inverse-actor integral sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRelativeCosetDomain.lean#L169-L180
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRelativeCosetDomain.lean#L169-L180

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
omit [Countable G]

theorem QEC.Coding.TannerLiftedProduct.lpsIndexedRelativeDomain_integral (H : Subgroup G) (s : Set α)
    (hs : IsFundamentalDomain G s μ) (e : I ≃ G ⧸ H) (r : I → G)
    (hr : ∀i,QuotientGroup.mk (r i)=e i) (F : α → E)
    (hF : ∀i,IntegrableOn F ((r i)⁻¹ • s) μ) :
    (∫x in ⋃i,(r i)⁻¹ • s,F x ∂μ)=∑i,∫x in s,F ((r i)⁻¹ • x) ∂μ := by sorry
