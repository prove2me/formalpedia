-- Prove2me | Theorems.Thm_P2M_Formalism_LT_Asm_FunEqGroup_of__ab8c5b9f22dd
-- name    : P2M_Formalism_LT_Asm_FunEqGroup_of__ab8c5b9f22dd
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:58:34.469837+00:00
-- url     : https://prove2.me/theorems/575e31f5-61c0-4c4a-94e0-80244d51b8ce
-- title:
--   P2 M Formalism LT Asm Fun Eq Group of  ab8c5b9f22dd: P2 M Formalism LT Asm Fun Eq Group of  ab8c5b9f22dd
-- statement:
--   The P2 M Formalism LT Asm Fun Eq Group of  ab8c5b9f22dd construction uses the P2 M Formalism LT Asm Fun Eq Group of  ab8c5b9f22dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L79-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L79-L92

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MapSubtypeInjective
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
open Formalism Formalism.LT Formalism.LT.Asm
open Formalism.G

theorem P2M_Formalism_LT_Asm_FunEqGroup_of__ab8c5b9f22dd (h1 : SolveExists.{u, 0}) (h2 : InvIntegralOfClass.{u, 0})
    (h3 : FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqGroup.{u} := by sorry

alias «Formalism».«LT».«Asm».«FunEqGroup_of'» := P2M_Formalism_LT_Asm_FunEqGroup_of__ab8c5b9f22dd
