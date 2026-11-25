-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_fderiv_phiM_lower
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.fderiv_phiM_lower
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:49:33.299248+00:00
-- url     : https://prove2.me/theorems/4e407357-b933-5775-becf-0786474e7dbe
-- title:
--   S7: fderiv phi M lower
-- statement:
--   The S7 construction uses the fderiv phi M lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/PhiPart.lean#L210-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/PhiPart.lean#L210-L218

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.fderiv_phiM_lower (μ : Fin n → ℤ) {z X : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n)
    (hX : IsLowerTri X) :
    fderiv ℂ (PhiM μ) z (X * z) = -(∑ a, (μ a : ℂ) * X a a) * PhiM μ z := by sorry
