-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_de_sq
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.de_sq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:11:19.010802+00:00
-- url     : https://prove2.me/theorems/9043fcd4-72b0-455b-90c3-2660a841fa22
-- title:
--   OSAux: de sq
-- statement:
--   The OSAux construction uses the de sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/RhoSqInsSucc.lean#L119-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/RhoSqInsSucc.lean#L119-L138

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqInsSucc
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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.de_sq {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) :
    de x l ^ 2 = (Lsq x l * rhoSq x l + (-(∑ i, ‖x.2.2.1 i‖ ^ 2) / 2 - (bS x l).re) ^ 2) +
      (x.2.2.2 - (bS x l).im) ^ 2 := by sorry
