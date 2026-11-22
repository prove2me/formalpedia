-- Prove2me | Theorems.Thm_P2M_Formalism_LFunctionChainParameters_characterSumData_PB_chC_apply__06e97235fe62
-- name    : P2M_Formalism_LFunctionChainParameters_characterSumData_PB_chC_apply__06e97235fe62
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:49:05.524799+00:00
-- url     : https://prove2.me/theorems/a2f61d08-88e6-4f5d-9440-150e51c1d618
-- title:
--   P2 M Formalism LFunction Chain Parameters character Sum Data PB ch C apply  06e97235fe62: P2 M Formalism LFunction Chain Parameters character Sum Data PB ch C apply  06e97235fe62
-- statement:
--   The P2 M Formalism LFunction Chain Parameters character Sum Data PB ch C apply  06e97235fe62 construction uses the P2 M Formalism LFunction Chain Parameters character Sum Data PB ch C apply  06e97235fe62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L85-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L85-L85

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.characterSumData
open Formalism Formalism.D5
open Formalism.LFunctionChainParameters.characterSumData.PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem P2M_Formalism_LFunctionChainParameters_characterSumData_PB_chC_apply__06e97235fe62 (g : E0 × H) : (chC : AddChar (E0 × H) ℂ) g = if g.1.1 = 0 then 1 else -1 := by sorry

alias «Formalism».«LFunctionChainParameters».«characterSumData».«PB».«chC_apply'» := P2M_Formalism_LFunctionChainParameters_characterSumData_PB_chC_apply__06e97235fe62
