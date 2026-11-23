-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_EulerCharacteristicLength_primitive_hasDerivAt
-- name    : ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength.primitive_hasDerivAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:30:13.133292+00:00
-- url     : https://prove2.me/theorems/55328941-7bae-4c82-b4c2-c8df4c1fb2b0
-- title:
--   Euler Characteristic Length: primitive has Deriv At
-- statement:
--   The Euler Characteristic Length construction uses the primitive has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/PrimZeroOfNonpos.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/PrimZeroOfNonpos.lean#L52-L53

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

theorem ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength.primitive_hasDerivAt (t : ℝ) : HasDerivAt P (expNegInvGlue t) t := by sorry
