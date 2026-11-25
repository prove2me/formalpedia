-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_uwr_fin_comp
-- name    : ReciprocityTheory.L2DbarEstimates.F.uwr_fin_comp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:57:48.123954+00:00
-- url     : https://prove2.me/theorems/549c9907-d4ab-5a2a-84a1-f24c62bdc2c6
-- title:
--   F: uwr fin comp
-- statement:
--   The F construction uses the uwr fin comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightRel.lean#L80-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightRel.lean#L80-L88

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

theorem ReciprocityTheory.L2DbarEstimates.F.uwr_fin_comp (f : M → V n) (p : M → ℝ) (hf : nV n z f p < ⊤) (k : Fin n) :
    ∫⁻ x, ENNReal.ofReal (‖f x k‖ ^ 2 * Real.exp (-p x)) ∂vol n z < ⊤ := by sorry
