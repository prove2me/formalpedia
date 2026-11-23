-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_chT_wd
-- name    : ReciprocityTheory.L2DbarEstimates.F.chT_wd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:30:49.068285+00:00
-- url     : https://prove2.me/theorems/bbbf37df-7dee-4a02-a4cc-38b7a6765396
-- title:
--   F: ch T wd
-- statement:
--   The F construction uses the ch T wd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/ChartA.lean#L137-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/ChartA.lean#L137-L147

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
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n} {e : OpenPartialHomeomorph M (V n)}

theorem ReciprocityTheory.L2DbarEstimates.F.chT_wd (ρ : V n → ℝ) (φ : V n → ℂ) (O : Set (V n)) (hOo : IsOpen O)
    (h1 : ∀ y ∈ O, ρ y = 1) (y : V n) (hy : y ∈ O) (j : Fin n) :
    wd n j (fun y => (ρ y : ℂ) * φ y) y = wd n j φ y ∧
      wdb n j (fun y => (ρ y : ℂ) * φ y) y = wdb n j φ y := by sorry
