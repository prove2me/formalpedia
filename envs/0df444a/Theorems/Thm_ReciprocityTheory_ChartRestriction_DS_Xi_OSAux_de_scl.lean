-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_de_scl
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.de_scl
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:49:52.065172+00:00
-- url     : https://prove2.me/theorems/729432fb-cbf4-589e-a4a3-07aa7a7bab70
-- title:
--   OSAux: de scl
-- statement:
--   The OSAux construction uses the de scl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/RhoSqNonneg.lean#L186-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/RhoSqNonneg.lean#L186-L206

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqNonneg
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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.de_scl {p m : ℕ} (τ : ℝ) (h1 : 1 ≤ τ) (h2 : τ ≤ 2) (x : Xp (p + 1) m) (l : Fin (p + 2)) :
    de x l / 2 ≤ de (scl τ x) l := by sorry
