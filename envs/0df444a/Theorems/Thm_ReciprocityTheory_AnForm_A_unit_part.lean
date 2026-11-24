-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_unit_part
-- name    : ReciprocityTheory.AnForm.A.unit_part
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:06.843668+00:00
-- url     : https://prove2.me/theorems/e3fe659b-8f46-4ab0-95df-235215f76ef0
-- title:
--   A: unit part
-- statement:
--   The A construction uses the unit part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/HasCompactSupportCompHypInclAt.lean#L227-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/HasCompactSupportCompHypInclAt.lean#L227-L258

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HasCompactSupportCompHypInclAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.AnForm.A.unit_part {U : Set (Fin (n + 1) → ℂ)} {v : (Fin (n + 1) → ℂ) → ℝ}
    {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hp : PoincareLelongData U v φ) {u : (Fin (n + 1) → ℂ) → ℂ}
    (hu : DifferentiableOn ℂ u U) (hu0 : ∀ z ∈ U, u z ≠ 0) :
    Integrable (fun z => Real.log ‖u z‖ * densV v φ z) ∧
      ∫ z, Real.log ‖u z‖ * densV v φ z = 0 := by sorry
