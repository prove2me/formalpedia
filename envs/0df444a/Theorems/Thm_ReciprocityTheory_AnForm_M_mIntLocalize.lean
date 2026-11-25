-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_mIntLocalize
-- name    : ReciprocityTheory.AnForm.M.mIntLocalize
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:38:13.81484+00:00
-- url     : https://prove2.me/theorems/cf0932d7-8fbb-4261-9eca-8ddd9b479dce
-- title:
--   M: m Int Localize
-- statement:
--   The M construction uses the m Int Localize property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegrableOnTargetOfTsupport.lean#L122-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegrableOnTargetOfTsupport.lean#L122-L133

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff
noncomputable section

theorem ReciprocityTheory.AnForm.M.mIntLocalize : MIntLocalizeStatement := by sorry
