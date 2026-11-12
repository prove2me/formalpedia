-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_actual_Y_binary
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.actual_Y_binary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T17:27:51.98897+00:00
-- url     : https://prove2.me/theorems/972c4359-0177-466d-a034-4c8901561da7
-- title:
--   BDL26 Transposed Stopped Decoder: actual Y binary
-- statement:
--   The raw binary Y representative is XZ, whereas its Hermitian operator has phase i.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L321-L324
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L321-L324

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Base
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TransposedStoppedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RZMap1CoordinateBridge MultiscaleDecoder
open PauliSymplectic BDL26CSSHamiltonian
open scoped Classical BigOperators

theorem QEC.Coding.BDL26TransposedStoppedDecoder.actual_Y_binary (S : OddScale) (n : Nat) (q : Physical S (n + 2)) :
    CSSDaviesLocality.singlePauli q .y =
      binaryMul (cssXCheck (Pi.single q 1)) (cssZCheck (Pi.single q 1)) := by sorry
