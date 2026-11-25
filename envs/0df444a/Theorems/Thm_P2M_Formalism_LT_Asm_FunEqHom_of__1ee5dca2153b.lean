-- Prove2me | Theorems.Thm_P2M_Formalism_LT_Asm_FunEqHom_of__1ee5dca2153b
-- name    : P2M_Formalism_LT_Asm_FunEqHom_of__1ee5dca2153b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:58:41.565805+00:00
-- url     : https://prove2.me/theorems/97874e2a-9834-4613-8c7f-3e93b2ab202f
-- title:
--   P2 M Formalism LT Asm Fun Eq Hom of  1ee5dca2153b: P2 M Formalism LT Asm Fun Eq Hom of  1ee5dca2153b
-- statement:
--   The P2 M Formalism LT Asm Fun Eq Hom of  1ee5dca2153b construction uses the P2 M Formalism LT Asm Fun Eq Hom of  1ee5dca2153b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L110-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L110-L117

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

theorem P2M_Formalism_LT_Asm_FunEqHom_of__1ee5dca2153b (h1 : SolveExists.{u, 0}) (h2 : InvIntegralOfClass.{u, 0})
    (h3 : FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqHom.{u} := by sorry

alias «Formalism».«LT».«Asm».«FunEqHom_of'» := P2M_Formalism_LT_Asm_FunEqHom_of__1ee5dca2153b
