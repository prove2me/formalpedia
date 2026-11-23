-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_chT_aem_symm
-- name    : ReciprocityTheory.L2DbarEstimates.F.chT_aem_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:32:49.578439+00:00
-- url     : https://prove2.me/theorems/0362cc19-dd30-455f-9be1-23f65010ccaf
-- title:
--   F: ch T aem symm
-- statement:
--   The F construction uses the ch T aem symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/ChartA.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/ChartA.lean#L16-L16

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ChartA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set Function
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M]
  [BorelSpace M] {n : ℕ} {z : M → V n} {e : OpenPartialHomeomorph M (V n)}

theorem ReciprocityTheory.L2DbarEstimates.F.chT_aem_symm : AEMeasurable (e.symm : V n → M) (volume.restrict e.target) := by sorry
