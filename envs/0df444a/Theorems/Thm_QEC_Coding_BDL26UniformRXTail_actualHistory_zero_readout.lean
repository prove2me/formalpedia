-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actualHistory_zero_readout
-- name    : QEC.Coding.BDL26UniformRXTail.actualHistory_zero_readout
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T10:34:38.552195+00:00
-- url     : https://prove2.me/theorems/3b16d249-ce31-4490-863d-8931f051ae3d
-- title:
--   BDL26 Uniform RXTail: actual History zero readout
-- statement:
--   Every physical readout is zero; length and correction snapshots are retained.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/StoppedReadout.lean#L33-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/StoppedReadout.lean#L33-L49

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_StoppedReadout
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26UniformRXTail.actualHistory_zero_readout (S : OddScale) (n : Nat)
    (sigma : (indexedFamily S (n + 2)).Syndrome (TopIndex (n + 2)))
    (hs : sigma.val = 0) (i : LevelIndex (n + 2)) :
    LevelTwoHistory.syndromeReadout (indexedDecoderData S (n + 2))
      (actualHistory S n sigma) i = 0 := by sorry
