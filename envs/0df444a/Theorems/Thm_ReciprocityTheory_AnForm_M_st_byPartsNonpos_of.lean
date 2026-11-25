-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_st_byPartsNonpos_of
-- name    : ReciprocityTheory.AnForm.M.st_byPartsNonpos_of
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:51:39.544826+00:00
-- url     : https://prove2.me/theorems/be6a4ced-2fb8-42ac-820b-19f0437a32b4
-- title:
--   M: st by Parts Nonpos of
-- statement:
--   The M construction uses the st by Parts Nonpos of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesD.lean#L270-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesD.lean#L270-L324

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.st_byPartsNonpos_of (hP : PartsStatement) (hN : GradDensNonnegStatement) :
    ByPartsNonposStatement := by sorry
