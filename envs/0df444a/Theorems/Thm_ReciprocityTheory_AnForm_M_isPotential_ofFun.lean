-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_isPotential_ofFun
-- name    : ReciprocityTheory.AnForm.M.isPotential_ofFun
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:52.665974+00:00
-- url     : https://prove2.me/theorems/e52a8882-a781-4b1b-84b2-56fc3fc1f520
-- title:
--   M: is Potential of Fun
-- statement:
--   The M construction uses the is Potential of Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IsPotentialOfFun.lean#L178-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IsPotentialOfFun.lean#L178-L181

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory
open scoped ContDiff
noncomputable section
open FinHolAtlas
variable {e : ℕ} {X : Type*} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.isPotential_ofFun (A : FinHolAtlas e X) (u : X → ℝ) (hu : A.Smooth u) :
    IsPotential A (LocPot.ofFun u) := by sorry
