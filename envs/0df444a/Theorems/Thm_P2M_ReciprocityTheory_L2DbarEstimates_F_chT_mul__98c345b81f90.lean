-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_F_chT_mul__98c345b81f90
-- name    : P2M_ReciprocityTheory_L2DbarEstimates_F_chT_mul__98c345b81f90
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:18:39.379951+00:00
-- url     : https://prove2.me/theorems/94e15147-cbb5-4279-a2a3-833814b92398
-- title:
--   P2 M Reciprocity Theory L2 Dbar Estimates F ch T mul  98c345b81f90: P2 M Reciprocity Theory L2 Dbar Estimates F ch T mul  98c345b81f90
-- statement:
--   The P2 M Reciprocity Theory L2 Dbar Estimates F ch T mul  98c345b81f90 construction uses the P2 M Reciprocity Theory L2 Dbar Estimates F ch T mul  98c345b81f90 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/ChartA.lean#L129-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/ChartA.lean#L129-L135

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

theorem P2M_ReciprocityTheory_L2DbarEstimates_F_chT_mul__98c345b81f90 (ρ : V n → ℝ) (hρd : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (U : Set (V n)) (hρt : tsupport ρ ⊆ U) (φ : V n → ℂ) (hφd : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun y => (ρ y : ℂ) * φ y) ∧ HasCompactSupport (fun y => (ρ y : ℂ) * φ y) ∧
      tsupport (fun y => (ρ y : ℂ) * φ y) ⊆ U := by sorry

alias «ReciprocityTheory».«L2DbarEstimates».«F».«chT_mulρ» := P2M_ReciprocityTheory_L2DbarEstimates_F_chT_mul__98c345b81f90
