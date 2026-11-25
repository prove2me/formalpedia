-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_regM_db_eq_zero_of_notMem
-- name    : ReciprocityTheory.L2DbarEstimates.F.regM_db_eq_zero_of_notMem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:56:37.236176+00:00
-- url     : https://prove2.me/theorems/1fb2f1b6-bbcf-5a53-b1b6-cbc03d8fb050
-- title:
--   F: reg M db eq zero of not Mem
-- statement:
--   The F construction uses the reg M db eq zero of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/HormanderEstimate/RegMDbEqZeroOfNotMem.lean#L48-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/HormanderEstimate/RegMDbEqZeroOfNotMem.lean#L48-L62

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegGlue
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_RegMDbEqZeroOfNotMem
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db

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

theorem ReciprocityTheory.L2DbarEstimates.F.regM_db_eq_zero_of_notMem {n : ℕ} (z : M → V n) (j : Fin n) (φ : M → ℂ) (x : M)
    (hx : x ∉ tsupport φ) : db n z j φ x = 0 := by sorry
