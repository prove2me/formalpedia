-- Prove2me | Theorems.Thm_P2M_Formalism_FG_CongrVAux_norm_sub_le_max__2892e70044d6
-- name    : P2M_Formalism_FG_CongrVAux_norm_sub_le_max__2892e70044d6
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:54:48.544319+00:00
-- url     : https://prove2.me/theorems/d552cf96-e539-46d0-9444-fd19dadad8f7
-- title:
--   P2 M Formalism FG Congr VAux norm sub le max  2892e70044d6: P2 M Formalism FG Congr VAux norm sub le max  2892e70044d6
-- statement:
--   The P2 M Formalism FG Congr VAux norm sub le max  2892e70044d6 construction uses the P2 M Formalism FG Congr VAux norm sub le max  2892e70044d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CongrV.lean#L127-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CongrV.lean#L127-L128

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.CongrVAux
open MvPowerSeries Formalism.G Formalism.LT Formalism.FG.SolveVAux
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {τ : Type w}

theorem P2M_Formalism_FG_CongrVAux_norm_sub_le_max__2892e70044d6 (a b : K) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by sorry

alias «Formalism».«FG».«CongrVAux».«norm_sub_le_max'» := P2M_Formalism_FG_CongrVAux_norm_sub_le_max__2892e70044d6
