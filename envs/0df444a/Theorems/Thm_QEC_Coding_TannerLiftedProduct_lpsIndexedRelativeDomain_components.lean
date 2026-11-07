-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIndexedRelativeDomain_components
-- name    : QEC.Coding.TannerLiftedProduct.lpsIndexedRelativeDomain_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:17:57.827243+00:00
-- url     : https://prove2.me/theorems/3bff8d6b-8596-49d8-9644-bc8210108035
-- title:
--   Tanner Lifted Product: lps Indexed Relative Domain components
-- statement:
--   Distinct true indexed section components are almost disjoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRelativeCosetDomain.lean#L156-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRelativeCosetDomain.lean#L156-L165

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
omit [Countable G] [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ] [Fintype I]

theorem QEC.Coding.TannerLiftedProduct.lpsIndexedRelativeDomain_components (H : Subgroup G) (s : Set α)
    (hs : IsFundamentalDomain G s μ) (e : I ≃ G ⧸ H) (r : I → G)
    (hr : ∀i,QuotientGroup.mk (r i)=e i) :
    Pairwise (fun i j => AEDisjoint μ ((r i)⁻¹ • s) ((r j)⁻¹ • s)) := by sorry
