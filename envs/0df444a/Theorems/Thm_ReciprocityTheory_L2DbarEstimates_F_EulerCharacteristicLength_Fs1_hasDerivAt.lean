-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_EulerCharacteristicLength_Fs1_hasDerivAt
-- name    : ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength.Fs1_hasDerivAt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:55:35.027267+00:00
-- url     : https://prove2.me/theorems/c8304bbb-42d9-452e-8d2d-40ced0ea4b35
-- title:
--   Euler Characteristic Length: Fs1 has Deriv At
-- statement:
--   The Euler Characteristic Length construction uses the Fs1 has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/PrimZeroOfNonpos.lean#L84-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/PrimZeroOfNonpos.lean#L84-L89

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

theorem ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength.Fs1_hasDerivAt (c : ℕ → ℝ) (a : ℝ) (m : ℕ) (t : ℝ) :
    HasDerivAt (Fs1 c a m) (Fs2 c a m t) t := by sorry
