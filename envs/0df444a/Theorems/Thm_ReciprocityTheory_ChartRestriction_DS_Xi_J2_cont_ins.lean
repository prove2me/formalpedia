-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_cont_ins
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.J2.cont_ins
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:10:53.156241+00:00
-- url     : https://prove2.me/theorems/3b3d9f86-6469-51fb-84e0-aba65416de7e
-- title:
--   J2: cont ins
-- statement:
--   The J2 construction uses the cont ins property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/CriticalExponentSucc.lean#L182-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/CriticalExponentSucc.lean#L182-L185

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_CriticalExponentSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Module
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2

theorem ReciprocityTheory.ChartRestriction.DS.Xi.J2.cont_ins (p m : ℕ) : Continuous fun z : ℂ × TDom p m =>
    ((z.2.1, Fin.cons z.1 z.2.2.1, z.2.2.2) : Xp (p + 1) m) := by sorry
