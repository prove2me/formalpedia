-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_integrable_fsDens
-- name    : ReciprocityTheory.AnForm.integrable_fsDens
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:09.688686+00:00
-- url     : https://prove2.me/theorems/6db1a92f-40ff-4183-b304-195eef31f70f
-- title:
--   An Form: integrable fs Dens
-- statement:
--   The An Form construction uses the integrable fs Dens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegralIoiFsDensRadial.lean#L168-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegralIoiFsDensRadial.lean#L168-L169

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegralIoiFsDensRadial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open MeasureTheory Filter Topology Set
noncomputable section

theorem ReciprocityTheory.AnForm.integrable_fsDens : Integrable fsDens := by sorry
