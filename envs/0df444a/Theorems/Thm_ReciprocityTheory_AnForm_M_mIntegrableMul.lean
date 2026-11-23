-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_mIntegrableMul
-- name    : ReciprocityTheory.AnForm.M.mIntegrableMul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:02.936839+00:00
-- url     : https://prove2.me/theorems/033a386e-d8fa-4064-848d-486be849ebcf
-- title:
--   M: m Integrable Mul
-- statement:
--   The M construction uses the m Integrable Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegrableOnTargetOfTsupport.lean#L139-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegrableOnTargetOfTsupport.lean#L139-L141

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

theorem ReciprocityTheory.AnForm.M.mIntegrableMul : MIntegrableMulStatement := by sorry
