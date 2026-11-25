-- Prove2me | Theorems.Thm_PI_RayBoundIQW_gen_ne_zero
-- name    : PI.RayBoundIQW.gen_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:19:11.098925+00:00
-- url     : https://prove2.me/theorems/1f02c453-3c55-50b4-b4b5-bf300a0f995d
-- title:
--   Ray Bound IQW: gen ne zero
-- statement:
--   The Ray Bound IQW construction uses the gen ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ImaginaryQuadraticClassBound/GenCoprime.lean#L55-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ImaginaryQuadraticClassBound/GenCoprime.lean#L55-L62

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

theorem PI.RayBoundIQW.gen_ne_zero (J : PrimeTo qq) : gen qq J ≠ 0 := by sorry
