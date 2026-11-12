-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dualHistory_zero_inputs
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.dualHistory_zero_inputs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T17:20:04.450642+00:00
-- url     : https://prove2.me/theorems/45487160-863d-4abb-a5ba-2f460361531d
-- title:
--   BDL26 Transposed Stopped Decoder: dual History zero inputs
-- statement:
--   A zero syndrome preserves all zero inputs without erasing chosen local cycles.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L56-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L56-L60

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.dualHistory_zero_inputs (S : OddScale) (n : Nat)
    (sigma : (dualFamily S (n + 2)).Syndrome (TopIndex (n + 2))) (hs : sigma.val = 0) :
    ∀ e ∈ dualHistory S n sigma, e.inputSyndrome.2.val = 0 := by sorry
