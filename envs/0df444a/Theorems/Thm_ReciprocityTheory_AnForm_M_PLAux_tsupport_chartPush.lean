-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_tsupport_chartPush
-- name    : ReciprocityTheory.AnForm.M.PLAux.tsupport_chartPush
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:19:27.575576+00:00
-- url     : https://prove2.me/theorems/0495c44b-f500-4edc-b6c8-9ae539ca077a
-- title:
--   PLAux: tsupport chart Push
-- statement:
--   The PLAux construction uses the tsupport chart Push property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCEqZeroOfEventuallyEqZero.lean#L165-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCEqZeroOfEventuallyEqZero.lean#L165-L170

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

theorem ReciprocityTheory.AnForm.M.PLAux.tsupport_chartPush [T2Space X] (ψ : OpenPartialHomeomorph X (Fin e → ℂ))
    {F : (Fin e → ℂ) → ℝ} (hK : IsCompact (tsupport F)) (hKt : tsupport F ⊆ ψ.target) :
    tsupport (chartPush ψ F) ⊆ ψ.symm '' tsupport F := by sorry
