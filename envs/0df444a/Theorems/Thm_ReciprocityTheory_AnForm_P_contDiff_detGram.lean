-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_P_contDiff_detGram
-- name    : ReciprocityTheory.AnForm.P.contDiff_detGram
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:40.822296+00:00
-- url     : https://prove2.me/theorems/11678896-f4e0-4cbe-ae61-3e490db67dd3
-- title:
--   P: cont Diff det Gram
-- statement:
--   The P construction uses the cont Diff det Gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDens.lean#L69-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDens.lean#L69-L110

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open MeasureTheory
noncomputable section
open Matrix Polynomial

theorem ReciprocityTheory.AnForm.P.contDiff_detGram (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) :
    ContDiff ℝ 2 (detGram N hd m hm) := by sorry
