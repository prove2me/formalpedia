-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actualStep_zero_coarse
-- name    : QEC.Coding.BDL26UniformRXTail.actualStep_zero_coarse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:55:58.179321+00:00
-- url     : https://prove2.me/theorems/7c2941c0-3969-49cf-bfb7-32e892f66fe1
-- title:
--   BDL26 Uniform RXTail: actual Step zero coarse
-- statement:
--   The BDL26 Uniform RXTail construction uses the actual Step zero coarse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/StoppedReadout.lean#L10-L22
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/StoppedReadout.lean#L10-L22

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_StoppedReadout
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26UniformRXTail.actualStep_zero_coarse (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (sigma : (indexedFamily S depth).Syndrome i.succ) (hs : sigma.val = 0) :
    (actualStep S depth i sigma).coarse.val = 0 := by sorry
