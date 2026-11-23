-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_phiM_tri_mul
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.phiM_tri_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:10:15.904503+00:00
-- url     : https://prove2.me/theorems/3b85b1ce-e00b-49fb-87f4-e6a4d0e278c7
-- title:
--   S7: phi M tri mul
-- statement:
--   The S7 construction uses the phi M tri mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/PhiFacts.lean#L115-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/PhiFacts.lean#L115-L132

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_Minors
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
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

theorem ReciprocityTheory.ChartRestriction.DS.S7.phiM_tri_mul (μ : Fin n → ℤ) {c z c' : Matrix (Fin n) (Fin n) ℂ} (hc : IsLowerTri c) (hc' : IsUpperTri c')
    (hcd : ∀ l, c l l ≠ 0) (hcd' : ∀ l, c' l l ≠ 0) (hz : z ∈ OmegaSet n) :
    c * z * c' ∈ OmegaSet n ∧
      PhiM μ (c * z * c') = (∏ l, (c l l * c' l l) ^ (-μ l)) * PhiM μ z := by sorry
