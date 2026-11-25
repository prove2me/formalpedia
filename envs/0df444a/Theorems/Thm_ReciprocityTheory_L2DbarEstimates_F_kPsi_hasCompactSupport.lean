-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_kPsi_hasCompactSupport
-- name    : ReciprocityTheory.L2DbarEstimates.F.kPsi_hasCompactSupport
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:03:03.79402+00:00
-- url     : https://prove2.me/theorems/a7fbf185-594a-5dac-a1ca-8f06a0f00a6e
-- title:
--   F: k Psi has Compact Support
-- statement:
--   The F construction uses the k Psi has Compact Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/KPsiHasCompactSupport.lean#L57-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/KPsiHasCompactSupport.lean#L57-L68

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_KPsiHasCompactSupport
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

theorem ReciprocityTheory.L2DbarEstimates.F.kPsi_hasCompactSupport {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (ph : M → ℝ) (φ : M → ℂ) (hφ : IsTest n z φ) (j k : Fin n) :
    HasCompactSupport (kPsi n z ph φ j k) := by sorry
