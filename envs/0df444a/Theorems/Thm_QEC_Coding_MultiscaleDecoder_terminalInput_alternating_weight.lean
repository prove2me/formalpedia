-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_terminalInput_alternating_weight
-- name    : QEC.Coding.MultiscaleDecoder.terminalInput_alternating_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:23:56.967458+00:00
-- url     : https://prove2.me/theorems/0170ed51-2431-41c5-a67a-ae0adf24d71f
-- title:
--   Multiscale Decoder: terminal Input alternating weight
-- statement:
--   Accumulate primitive global RX/RZ inequalities through actual selected inputs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L926-L966
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L926-L966

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open scoped BigOperators
universe u v w x y z
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]

theorem QEC.Coding.MultiscaleDecoder.terminalInput_alternating_weight
    (D : BDL26DecoderData depth C0 C1 C2) (S : AlternatingStepData D)
    (hstep : ∀ (i : StepIndex depth) (s : D.family.Syndrome i.succ),
      if i.val % 2 = 0 then
        2 * HammingWeight (S.step i s).coarse.val ≤ HammingWeight s.val
      else HammingWeight (S.step i s).coarse.val ≤ HammingWeight s.val)
    (sigma : D.family.Syndrome (TopIndex depth)) :
    2 ^ ((depth + 1) / 2) * HammingWeight (terminalInput D S sigma).val ≤
      HammingWeight sigma.val := by sorry
