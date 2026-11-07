-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsRelativeDomain_integral
-- name    : QEC.Coding.TannerLiftedProduct.lpsRelativeDomain_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:05:02.643933+00:00
-- url     : https://prove2.me/theorems/50a14da9-f971-4b18-9a1d-e6b6c79c6000
-- title:
--   Tanner Lifted Product: lps Relative Domain integral
-- statement:
--   Integrate the true finite-index cover as inverse-actor component integrals.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRelativeCosetDomain.lean#L103-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRelativeCosetDomain.lean#L103-L117

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

theorem QEC.Coding.TannerLiftedProduct.lpsRelativeDomain_integral (H : Subgroup G) (s : Set α)
    [H.FiniteIndex] (r : G ⧸ H → G)
    (hr : ∀c, QuotientGroup.mk (r c) = c) (hs : IsFundamentalDomain G s μ) (F : α → E)
    (hF : ∀c, IntegrableOn F ((r c)⁻¹ • s) μ) :
    (∫τ in lpsRelativeDomain H s r, F τ ∂μ) =
      ∑' c, ∫τ in s, F ((r c)⁻¹ • τ) ∂μ := by sorry
