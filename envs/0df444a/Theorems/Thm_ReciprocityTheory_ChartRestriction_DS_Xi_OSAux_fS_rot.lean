-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_fS_rot
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.fS_rot
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:53:24.128795+00:00
-- url     : https://prove2.me/theorems/a4b40734-4cef-581a-ba4c-0ffe6b25abe8
-- title:
--   OSAux: f S rot
-- statement:
--   The OSAux construction uses the f S rot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/OscillatoryBound.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/OscillatoryBound.lean#L30-L32

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.fS_rot {p m : ℕ} (s : Fin (p + 2) → ℝ) (t : ℝ) (x : Xp (p + 1) m) : fS s (rot t x) = fS s x := by sorry
