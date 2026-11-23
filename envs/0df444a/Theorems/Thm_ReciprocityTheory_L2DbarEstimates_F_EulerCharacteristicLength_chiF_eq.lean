-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_EulerCharacteristicLength_chiF_eq
-- name    : ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength.chiF_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:30:01.7195+00:00
-- url     : https://prove2.me/theorems/1ccf1017-fe43-45e4-80a1-721cb8828ee6
-- title:
--   Euler Characteristic Length: chi F eq
-- statement:
--   The Euler Characteristic Length construction uses the chi F eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/PrimZeroOfNonpos.lean#L97-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/PrimZeroOfNonpos.lean#L97-L103

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

theorem ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength.chiF_eq {c : ℕ → ℝ} {a t : ℝ} {m : ℕ} (ht : t < a + m) : chiF c a t = Fs c a m t := by sorry
