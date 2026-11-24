-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_mInt_congr
-- name    : ReciprocityTheory.AnForm.M.PLAux.mInt_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:05.015034+00:00
-- url     : https://prove2.me/theorems/b49f5529-3ba3-43ac-9b51-b418f468aaa0
-- title:
--   PLAux: m Int congr
-- statement:
--   The PLAux construction uses the m Int congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCEqZeroOfEventuallyEqZero.lean#L32-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCEqZeroOfEventuallyEqZero.lean#L32-L43

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.M.PLAux
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.PLAux.mInt_congr {A : FinHolAtlas e X} {Φ Ψ : Fin e → LocPot X} {g g' : X → ℝ}
    (h : ∀ j, ∀ y ∈ (A.chart j).target,
      g ((A.chart j).symm y) * locDens A Φ j y = g' ((A.chart j).symm y) * locDens A Ψ j y) :
    mInt A Φ g = mInt A Ψ g' := by sorry
