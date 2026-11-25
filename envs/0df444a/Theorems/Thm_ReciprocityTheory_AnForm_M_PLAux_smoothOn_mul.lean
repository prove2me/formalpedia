-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_smoothOn_mul
-- name    : ReciprocityTheory.AnForm.M.PLAux.smoothOn_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:19:25.847165+00:00
-- url     : https://prove2.me/theorems/e1f8f120-4b1c-4f0c-bab4-eee05a0c7f8d
-- title:
--   PLAux: smooth On mul
-- statement:
--   The PLAux construction uses the smooth On mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCEqZeroOfEventuallyEqZero.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCEqZeroOfEventuallyEqZero.lean#L25-L26

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

theorem ReciprocityTheory.AnForm.M.PLAux.smoothOn_mul {A : FinHolAtlas e X} {U : Set X} {f g : X → ℝ} (hf : A.SmoothOn U f)
    (hg : A.SmoothOn U g) : A.SmoothOn U (fun x => f x * g x) := by sorry
