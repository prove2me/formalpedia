-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_uwr_boundS
-- name    : ReciprocityTheory.L2DbarEstimates.F.uwr_boundS
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:57:40.039838+00:00
-- url     : https://prove2.me/theorems/7123a188-c468-5cc4-99e7-61b80d028a8c
-- title:
--   F: uwr bound S
-- statement:
--   The F construction uses the uwr bound S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightRel.lean#L155-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightRel.lean#L155-L177

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

theorem ReciprocityTheory.L2DbarEstimates.F.uwr_boundS (E s t α q P N : ℝ) (hE : 0 < E) (hq : 0 ≤ q)
    (hsq : s ^ 2 ≤ 2 * q) (hN0 : 0 ≤ N) (hN : N ≤ E * (s + 2 * α * t)) :
    N ^ 2 ≤ (4 * E ^ 2 * Real.exp P + 8 * E * α ^ 2) * (q * Real.exp (-P) + t ^ 2 * E) := by sorry
