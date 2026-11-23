-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_two_le_infty
-- name    : ReciprocityTheory.AnForm.M.two_le_infty
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:12.966605+00:00
-- url     : https://prove2.me/theorems/0ca1cc71-8b93-4f05-b0f8-20260a37162c
-- title:
--   M: two le infty
-- statement:
--   The M construction uses the two le infty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PshShiftB.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PshShiftB.lean#L13-L19

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Filter Topology FinHolAtlas
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := by sorry
