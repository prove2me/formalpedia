-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_gram_upper_unique
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.MI.gram_upper_unique
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:12.337691+00:00
-- url     : https://prove2.me/theorems/d59f2335-f03b-4b5f-be5e-d6b8d99bc7b3
-- title:
--   MI: gram upper unique
-- statement:
--   The MI construction uses the gram upper unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfH.lean#L29-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfH.lean#L29-L88

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix
open scoped ComplexConjugate
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.MI.gram_upper_unique {ε : Fin n → ℂ} (hε : ∀ a, ε a * ε a = 1)
    {β β' : Matrix (Fin n) (Fin n) ℂ} (hβ : β.BlockTriangular id) (hβ' : β'.BlockTriangular id)
    (hd : β.det ≠ 0) (hd' : β'.det ≠ 0)
    (h : β'ᵀ * diagonal ε * β'.map (starRingEnd ℂ) = βᵀ * diagonal ε * β.map (starRingEnd ℂ)) :
    ∃ D : Fin n → ℂ, (∀ a, ‖D a‖ = 1) ∧ β' = diagonal D * β := by sorry
