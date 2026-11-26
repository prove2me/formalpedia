-- Prove2me | Theorems.Thm_P2M_NormOnePowProof_coe___9ed0e2e30865
-- name    : P2M_NormOnePowProof_coe___9ed0e2e30865
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:43:26.677612+00:00
-- url     : https://prove2.me/theorems/88b978d9-03b5-492b-bae7-7627a080dc23
-- title:
--   P2 M Norm One Pow Proof coe   9ed0e2e30865: P2 M Norm One Pow Proof coe   9ed0e2e30865
-- statement:
--   The P2 M Norm One Pow Proof coe   9ed0e2e30865 construction uses the P2 M Norm One Pow Proof coe   9ed0e2e30865 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormOnePowerPrincipal/PowPrincipal.lean#L14-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormOnePowerPrincipal/PowPrincipal.lean#L14-L14

import Definitions.Def_Formalism_PeriodIntegrals_NormOnePow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormOnePowerPrincipal_PowPrincipal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors
open NormOnePowProof
variable {E : Type} [Field E] [NumberField E]

theorem P2M_NormOnePowProof_coe___9ed0e2e30865 (c : E →+* E) (y : 𝓞 E) : ((σ c y : 𝓞 E) : E) = c (y : E) := by sorry

alias «NormOnePowProof».«coe_σ» := P2M_NormOnePowProof_coe___9ed0e2e30865
