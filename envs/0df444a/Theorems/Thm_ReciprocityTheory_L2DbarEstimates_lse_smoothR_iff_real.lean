-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_lse_smoothR_iff_real
-- name    : ReciprocityTheory.L2DbarEstimates.lse_smoothR_iff_real
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:02:13.376041+00:00
-- url     : https://prove2.me/theorems/39db73be-1109-53ef-8079-b70af65ecd11
-- title:
--   L2 Dbar Estimates: lse smooth R iff real
-- statement:
--   The L2 Dbar Estimates construction uses the lse smooth R iff real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/NormFibrations/LseSmoothRIffReal.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/NormFibrations/LseSmoothRIffReal.lean#L17-L24

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_LseSmoothRIffReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open Filter Topology
open scoped ContDiff

theorem ReciprocityTheory.L2DbarEstimates.lse_smoothR_iff_real {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℝ) :
    SmoothR n z f ↔ ∀ e : OpenPartialHomeomorph M (V n), IsChart n z e →
      ContDiffOn ℝ ∞ (f ∘ e.symm) e.target := by sorry
