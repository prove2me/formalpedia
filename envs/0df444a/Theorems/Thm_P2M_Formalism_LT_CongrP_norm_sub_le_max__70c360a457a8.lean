-- Prove2me | Theorems.Thm_P2M_Formalism_LT_CongrP_norm_sub_le_max__70c360a457a8
-- name    : P2M_Formalism_LT_CongrP_norm_sub_le_max__70c360a457a8
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:58:33.598812+00:00
-- url     : https://prove2.me/theorems/413cd9e1-1fdb-45b7-af74-0e1964c1fa31
-- title:
--   P2 M Formalism LT Congr P norm sub le max  70c360a457a8: P2 M Formalism LT Congr P norm sub le max  70c360a457a8
-- statement:
--   The P2 M Formalism LT Congr P norm sub le max  70c360a457a8 construction uses the P2 M Formalism LT Congr P norm sub le max  70c360a457a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/CoeffSubstAddCMulXPow.lean#L95-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/CoeffSubstAddCMulXPow.lean#L95-L97

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_CoeffSubstAddCMulXPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.CongrP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem P2M_Formalism_LT_CongrP_norm_sub_le_max__70c360a457a8 (a b : K) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by sorry

alias «Formalism».«LT».«CongrP».«norm_sub_le_max'» := P2M_Formalism_LT_CongrP_norm_sub_le_max__70c360a457a8
