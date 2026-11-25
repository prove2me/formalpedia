-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_EulerCharacteristicLength_Fs_contDiff
-- name    : ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength.Fs_contDiff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:55:10.880325+00:00
-- url     : https://prove2.me/theorems/b5121037-c129-48cd-8335-a484ac6d69cf
-- title:
--   Euler Characteristic Length: Fs cont Diff
-- statement:
--   The Euler Characteristic Length construction uses the Fs cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/PrimZeroOfNonpos.lean#L91-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/PrimZeroOfNonpos.lean#L91-L93

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_PrimZeroOfNonpos
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
open ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength

theorem ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength.Fs_contDiff (c : ℕ → ℝ) (a : ℝ) (m : ℕ) : ContDiff ℝ ∞ (Fs c a m) := by sorry
