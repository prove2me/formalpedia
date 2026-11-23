-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_byPartsNonpos
-- name    : ReciprocityTheory.AnForm.M.byPartsNonpos
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:58:35.467562+00:00
-- url     : https://prove2.me/theorems/812a7b7d-798b-417f-9f05-b36fa5cd0202
-- title:
--   M: by Parts Nonpos
-- statement:
--   The M construction uses the by Parts Nonpos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/Stokes.lean#L82-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/Stokes.lean#L82-L83

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesD
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
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

theorem ReciprocityTheory.AnForm.M.byPartsNonpos : ByPartsNonposStatement := by sorry
