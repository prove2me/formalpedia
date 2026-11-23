-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_sqNorm_entry_le_two_mul
-- name    : ReciprocityTheory.L2DbarEstimates.F.sqNorm_entry_le_two_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:30:59.828799+00:00
-- url     : https://prove2.me/theorems/0809a1f6-32b1-4e96-b3c6-e72d8536f0da
-- title:
--   F: sq Norm entry le two mul
-- statement:
--   The F construction uses the sq Norm entry le two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightRel.lean#L27-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightRel.lean#L27-L36

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightRel
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

theorem ReciprocityTheory.L2DbarEstimates.F.sqNorm_entry_le_two_mul (σ : Fin n → Fin n → ℂ) (j k : Fin n) : ‖σ j k‖ ^ 2 ≤ 2 * sq2 n σ := by sorry
