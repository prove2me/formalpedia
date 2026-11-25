-- Prove2me | Theorems.Thm_PI_RayBoundIQW_HData_le
-- name    : PI.RayBoundIQW.HData.le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:16.49928+00:00
-- url     : https://prove2.me/theorems/008efd04-d023-490f-b23b-08331c091c23
-- title:
--   HData: le
-- statement:
--   The HData construction uses the le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ImaginaryQuadraticClassBound/ClassNum.lean#L45-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ImaginaryQuadraticClassBound/ClassNum.lean#L45-L72

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ImaginaryQuadraticClassBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ImaginaryQuadraticClassBound_ClassNum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors
open PI PI.RayBoundIQW
variable {R : Type*} [CommRing R]

theorem PI.RayBoundIQW.HData.le {I J : Ideal R} {e1 e2 : R} {a c b : ℕ}
    (hspan : ∀ z : R, ∃ x y : ℤ, z = (x : R) * e1 + (y : R) * e2)
    (hP : HData I e1 e2 a c b) (haJ : ((a : ℤ) : R) * e1 ∈ J)
    (hbJ : ((b : ℤ) : R) * e1 + ((c : ℤ) : R) * e2 ∈ J) : I ≤ J := by sorry
