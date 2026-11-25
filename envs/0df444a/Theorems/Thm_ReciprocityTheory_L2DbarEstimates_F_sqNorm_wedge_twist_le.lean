-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_sqNorm_wedge_twist_le
-- name    : ReciprocityTheory.L2DbarEstimates.F.sqNorm_wedge_twist_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:03:17.7318+00:00
-- url     : https://prove2.me/theorems/927c26a5-f27a-440b-9695-e7fcfff5abc6
-- title:
--   F: sq Norm wedge twist le
-- statement:
--   The F construction uses the sq Norm wedge twist le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightBackA.lean#L89-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightBackA.lean#L89-L132

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackA
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

theorem ReciprocityTheory.L2DbarEstimates.F.sqNorm_wedge_twist_le {n : ℕ} (a : ℂ) (A : Fin n → Fin n → ℂ) (c : Fin n → ℂ) (B : V n) :
    sq2 n (fun j k => a * A j k + a * wedge c (fun i => B i) j k) ≤
      ‖a‖ ^ 2 * (2 + 4 * ∑ j, ‖c j‖ ^ 2) * (sq2 n A + ‖B‖ ^ 2) := by sorry
