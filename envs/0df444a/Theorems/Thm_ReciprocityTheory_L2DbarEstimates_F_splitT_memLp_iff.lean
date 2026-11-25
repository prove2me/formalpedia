-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_splitT_memLp_iff
-- name    : ReciprocityTheory.L2DbarEstimates.F.splitT_memLp_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:58:58.296076+00:00
-- url     : https://prove2.me/theorems/4722bec9-94af-4cdb-8059-3cc6f0f37dd8
-- title:
--   F: split T mem Lp iff
-- statement:
--   The F construction uses the split T mem Lp iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/SplitTest.lean#L46-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/SplitTest.lean#L46-L69

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_SplitTest
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

theorem ReciprocityTheory.L2DbarEstimates.F.splitT_memLp_iff {E : Type*} [NormedAddCommGroup E] (ph : M → ℝ) (hph : Continuous ph)
    (u : M → E) (hu : AEStronglyMeasurable u (vol n z)) :
    MemLp u 2 (wvol n z ph) ↔
      ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) ∂vol n z < ⊤ := by sorry
