-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_regM_lintegral_image
-- name    : ReciprocityTheory.L2DbarEstimates.F.regM_lintegral_image
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:57:49.283285+00:00
-- url     : https://prove2.me/theorems/62659e43-3db4-58ec-aca9-10426b112308
-- title:
--   F: reg M lintegral image
-- statement:
--   The F construction uses the reg M lintegral image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/HormanderEstimate/RegMDbEqZeroOfNotMem.lean#L64-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/HormanderEstimate/RegMDbEqZeroOfNotMem.lean#L64-L84

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegGlue
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_RegMDbEqZeroOfNotMem
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

theorem ReciprocityTheory.L2DbarEstimates.F.regM_lintegral_image {n : ℕ} (z : M → V n) (hz : IsLocalHomeomorph z)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (f : M → ℝ≥0∞) (hf : Measurable f)
    (K : Set (V n)) (hK : IsCompact K) (hKt : K ⊆ e.target) :
    ∫⁻ y in K, f (e.symm y) = ∫⁻ x in e.symm '' K, f x ∂vol n z := by sorry
