-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_log_norm_integral_at_coordinate
-- name    : ReciprocityTheory.AnForm.A.log_norm_integral_at_coordinate
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:01:27.918371+00:00
-- url     : https://prove2.me/theorems/50dea5ae-30aa-4926-aa12-4f728001635b
-- title:
--   A: log norm integral at coordinate
-- statement:
--   The A construction uses the log norm integral at coordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/HasCompactSupportCompHypInclAt.lean#L191-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/HasCompactSupportCompHypInclAt.lean#L191-L212

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

theorem ReciprocityTheory.AnForm.A.log_norm_integral_at_coordinate (n : ℕ) (i : Fin (n + 1)) (U : Set (Fin (n + 1) → ℂ))
    (v : (Fin (n + 1) → ℂ) → ℝ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (hp : PoincareLelongData U v φ) :
    Integrable (fun z => Real.log ‖z i‖ * densV v φ z) volume ∧
    Integrable (fun w => v (hypInclAt i w) * densHypAt i φ w) volume ∧
    ∫ z, Real.log ‖z i‖ * densV v φ z = ∫ w, v (hypInclAt i w) * densHypAt i φ w := by sorry
