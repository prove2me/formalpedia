-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_regM_of_measurable
-- name    : ReciprocityTheory.L2DbarEstimates.F.regM_of_measurable
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:59:13.970998+00:00
-- url     : https://prove2.me/theorems/fb10b4c3-739b-5a7a-8fcc-16e5eff5330a
-- title:
--   F: reg M of measurable
-- statement:
--   The F construction uses the reg M of measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/HormanderEstimate/RegMDbEqZeroOfNotMem.lean#L148-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/HormanderEstimate/RegMDbEqZeroOfNotMem.lean#L148-L218

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

theorem ReciprocityTheory.L2DbarEstimates.F.regM_of_measurable {n : ℕ} (hReg : C.RegStatement) (hExt : ExtendStatement n M)
    (z : M → V n) (hz : IsLocalHomeomorph z) (F : M → ℂ) (hFm : Measurable F)
    (hF : LocalL2Isometry (vol n z) F)
    (hw : ∀ φ : M → ℂ, IsTest n z φ → ∀ j : Fin n, ∫ x, F x * db n z j φ x ∂vol n z = 0) :
    ∃ G : M → ℂ, Holo n z G ∧ F =ᵐ[vol n z] G := by sorry
