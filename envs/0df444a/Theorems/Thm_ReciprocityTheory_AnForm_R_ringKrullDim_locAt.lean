-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_ringKrullDim_locAt
-- name    : ReciprocityTheory.AnForm.R.ringKrullDim_locAt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:47:38.532317+00:00
-- url     : https://prove2.me/theorems/2d355c73-e873-5d39-badc-77b7f0bd124f
-- title:
--   R: ring Krull Dim loc At
-- statement:
--   The R construction uses the ring Krull Dim loc At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChartA.lean#L24-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChartA.lean#L24-L77

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial Algebra

theorem ReciprocityTheory.AnForm.R.ringKrullDim_locAt {σ : Type} (J : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ)
    (hJ : J ≤ ptIdealOf z) :
    ringKrullDim (locAt J z) = ((ptIdealOf z).map (Ideal.Quotient.mk J)).height := by sorry
