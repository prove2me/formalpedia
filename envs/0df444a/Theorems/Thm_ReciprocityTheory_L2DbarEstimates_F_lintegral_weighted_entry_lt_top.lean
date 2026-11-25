-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_lintegral_weighted_entry_lt_top
-- name    : ReciprocityTheory.L2DbarEstimates.F.lintegral_weighted_entry_lt_top
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:55:53.113883+00:00
-- url     : https://prove2.me/theorems/d95215a6-4932-5b44-9fe3-9b9a49e371de
-- title:
--   F: lintegral weighted entry lt top
-- statement:
--   The F construction uses the lintegral weighted entry lt top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightRel.lean#L90-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightRel.lean#L90-L101

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightRel
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n}

theorem ReciprocityTheory.L2DbarEstimates.F.lintegral_weighted_entry_lt_top (σ : M → Fin n → Fin n → ℂ) (p : M → ℝ) (hσ : n2 n z σ p < ⊤) (j k : Fin n) :
    ∫⁻ x, ENNReal.ofReal (‖σ x j k‖ ^ 2 * Real.exp (-p x)) ∂vol n z < ⊤ := by sorry
