-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_fS_scl
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.fS_scl
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:49:46.034251+00:00
-- url     : https://prove2.me/theorems/1b226b58-8a43-4f2c-8200-e45832c46ca4
-- title:
--   OSAux: f S scl
-- statement:
--   The OSAux construction uses the f S scl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/OscillatoryBound.lean#L13-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/OscillatoryBound.lean#L13-L28

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExponentConditionNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoMulStar
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_OscillatoryBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux

theorem ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.fS_scl {p m : ℕ} (s : Fin (p + 2) → ℝ) (hs0 : ∀ l, 0 ≤ s l) (τ : ℝ) (hτ : τ ∈ Icc (1 : ℝ) 2)
    (x : Xp (p + 1) m) : fS s (scl τ x) ≤ ENNReal.ofReal (2 ^ ∑ l, s l) * fS s x := by sorry
