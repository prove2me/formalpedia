-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_gm_ipV_single
-- name    : ReciprocityTheory.L2DbarEstimates.F.gm_ipV_single
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:33:41.641322+00:00
-- url     : https://prove2.me/theorems/c5e388ea-926c-4938-a5b4-68de24eafd37
-- title:
--   F: gm ip V single
-- statement:
--   The F construction uses the gm ip V single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/HormanderEstimate/GmSingleIsTestForm.lean#L485-L497
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/HormanderEstimate/GmSingleIsTestForm.lean#L485-L497

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_GmSingleIsTestForm
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj

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
  [MeasurableSpace M] [BorelSpace M]

theorem ReciprocityTheory.L2DbarEstimates.F.gm_ipV_single (n : ℕ) (z : M → V n) (ph : M → ℝ) (F0 φ : M → ℂ) (j : Fin n) :
    ipV n z (dbarF n z F0) (gmSingle ph φ j) ph = conj (∫ x, db n z j F0 x * φ x ∂vol n z) := by sorry
