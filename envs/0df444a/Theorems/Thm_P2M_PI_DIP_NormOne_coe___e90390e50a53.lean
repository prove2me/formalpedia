-- Prove2me | Theorems.Thm_P2M_PI_DIP_NormOne_coe___e90390e50a53
-- name    : P2M_PI_DIP_NormOne_coe___e90390e50a53
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:42:54.215224+00:00
-- url     : https://prove2.me/theorems/917a2109-5fbb-528e-9293-e7c4b997af6c
-- title:
--   P2 M PI DIP Norm One coe   e90390e50a53: P2 M PI DIP Norm One coe   e90390e50a53
-- statement:
--   The P2 M PI DIP Norm One coe   e90390e50a53 construction uses the P2 M PI DIP Norm One coe   e90390e50a53 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantIdentity/NormOne.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantIdentity/NormOne.lean#L16-L16

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DetIdPG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_StNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_NormOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors
open PI PI.DIP PI.DIP.NormOne
variable {E : Type} [Field E] [NumberField E]

theorem P2M_PI_DIP_NormOne_coe___e90390e50a53 (c : E →+* E) (y : 𝓞 E) : ((σ c y : 𝓞 E) : E) = c (y : E) := by sorry

alias «PI».«DIP».«NormOne».«coe_σ» := P2M_PI_DIP_NormOne_coe___e90390e50a53
