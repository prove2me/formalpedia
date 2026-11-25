-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_piece_norm
-- name    : ReciprocityTheory.AnForm.M.pushA_piece_norm
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:04:19.515834+00:00
-- url     : https://prove2.me/theorems/b6609dd4-fb36-58eb-b161-69be881c9d4f
-- title:
--   M: push A piece norm
-- statement:
--   The M construction uses the push A piece norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PushAFinsumInter.lean#L149-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PushAFinsumInter.lean#L149-L156

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.pushA_piece_norm (q : X → Fin e → ℂ) (s : (Fin e → ℂ) → X) {D : Set (Fin e → ℂ)}
    (hinj : Set.InjOn (q ∘ s) D) (k : X → ℝ) (y : Fin e → ℂ) :
    ‖∑ᶠ x ∈ q ⁻¹' {y} ∩ s '' D, k x‖ = ∑ᶠ x ∈ q ⁻¹' {y} ∩ s '' D, |k x| := by sorry
