-- Prove2me | Theorems.Thm_PI_RayBoundIQW_gen_coprime
-- name    : PI.RayBoundIQW.gen_coprime
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:19:21.159302+00:00
-- url     : https://prove2.me/theorems/0a211fd9-5991-4a17-9a4a-bf7b50e46289
-- title:
--   Ray Bound IQW: gen coprime
-- statement:
--   The Ray Bound IQW construction uses the gen coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ImaginaryQuadraticClassBound/GenCoprime.lean#L64-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ImaginaryQuadraticClassBound/GenCoprime.lean#L64-L67

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

theorem PI.RayBoundIQW.gen_coprime (J : PrimeTo qq) : Ideal.span {gen qq J} ⊔ qq = ⊤ := by sorry
