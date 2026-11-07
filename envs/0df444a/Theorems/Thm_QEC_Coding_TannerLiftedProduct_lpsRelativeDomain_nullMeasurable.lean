-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsRelativeDomain_nullMeasurable
-- name    : QEC.Coding.TannerLiftedProduct.lpsRelativeDomain_nullMeasurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:17:44.109631+00:00
-- url     : https://prove2.me/theorems/b68a347f-ccd9-4e9d-b287-5fa99ba88543
-- title:
--   Tanner Lifted Product: lps Relative Domain null Measurable
-- statement:
--   Countable inverse translates of a true fundamental domain are null measurable.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRelativeCosetDomain.lean#L27-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRelativeCosetDomain.lean#L27-L32

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

theorem QEC.Coding.TannerLiftedProduct.lpsRelativeDomain_nullMeasurable (H : Subgroup G) (s : Set α)
    (r : G ⧸ H → G) (hs : IsFundamentalDomain G s μ) :
    NullMeasurableSet (lpsRelativeDomain H s r) μ := by sorry
