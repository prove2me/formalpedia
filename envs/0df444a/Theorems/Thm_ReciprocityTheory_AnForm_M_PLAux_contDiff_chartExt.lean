-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_contDiff_chartExt
-- name    : ReciprocityTheory.AnForm.M.PLAux.contDiff_chartExt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:19:33.874451+00:00
-- url     : https://prove2.me/theorems/68b8b080-a66f-4161-bf2c-9ab7bfa03804
-- title:
--   PLAux: cont Diff chart Ext
-- statement:
--   The PLAux construction uses the cont Diff chart Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCEqZeroOfEventuallyEqZero.lean#L210-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCEqZeroOfEventuallyEqZero.lean#L210-L238

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

theorem ReciprocityTheory.AnForm.M.PLAux.contDiff_chartExt [T2Space X] [CompactSpace X] {A : FinHolAtlas e X}
    {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ) {v : X → ℝ}
    (hv : A.Smooth v) (hvs : tsupport v ⊆ ψ.source) :
    ContDiff ℝ ∞ (chartExt ψ v) ∧ IsCompact (ψ '' tsupport v) ∧
      tsupport (chartExt ψ v) ⊆ ψ '' tsupport v := by sorry
