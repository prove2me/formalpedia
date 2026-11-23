-- Prove2me | Theorems.Thm_PI_RayBoundIQW_gen_spec
-- name    : PI.RayBoundIQW.gen_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:39.326744+00:00
-- url     : https://prove2.me/theorems/b8989800-2432-4c31-9727-17564b956941
-- title:
--   Ray Bound IQW: gen spec
-- statement:
--   The Ray Bound IQW construction uses the gen spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ImaginaryQuadraticClassBound/GenCoprime.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ImaginaryQuadraticClassBound/GenCoprime.lean#L51-L53

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ImaginaryQuadraticClassBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ImaginaryQuadraticClassBound_GenCoprime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open PI PI.RayBoundIQW
variable {K0 : Type} [Field K0] [NumberField K0] (qq : Ideal (𝓞 K0))

theorem PI.RayBoundIQW.gen_spec (J : PrimeTo qq) :
    Ideal.span {gen qq J} = J.1 * (base qq (cls qq J)).1 ^ (classNumber K0 - 1) := by sorry
