-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_regM_weakHolo
-- name    : ReciprocityTheory.L2DbarEstimates.F.regM_weakHolo
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:59:09.988855+00:00
-- url     : https://prove2.me/theorems/471ea666-a748-5bc4-a583-de4edd5243e7
-- title:
--   F: reg M weak Holo
-- statement:
--   The F construction uses the reg M weak Holo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/HormanderEstimate/RegMDbEqZeroOfNotMem.lean#L107-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/HormanderEstimate/RegMDbEqZeroOfNotMem.lean#L107-L146

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

theorem ReciprocityTheory.L2DbarEstimates.F.regM_weakHolo {n : ℕ} (hExt : ExtendStatement n M) (z : M → V n)
    (hz : IsLocalHomeomorph z) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e)
    (F : M → ℂ) (hFm : Measurable F) (hF : LocalL2Isometry (vol n z) F)
    (hw : ∀ φ : M → ℂ, IsTest n z φ → ∀ j : Fin n, ∫ x, F x * db n z j φ x ∂vol n z = 0) :
    C.WeakHolo e.target (F ∘ e.symm) := by sorry
