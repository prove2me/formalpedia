-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_singleton_xSyndrome_ne_zero
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.singleton_xSyndrome_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:33:24.669319+00:00
-- url     : https://prove2.me/theorems/3605e01d-167c-485c-b825-688b34ff7cbc
-- title:
--   BDL26 Transposed Stopped Decoder: singleton x Syndrome ne zero
-- statement:
--   Every actual physical singleton also has a nonzero original X-check syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L350-L361
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L350-L361

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.singleton_xSyndrome_ne_zero (S : OddScale) (n : Nat) (q : Physical S n) :
    xSyndrome S n (Pi.single q 1) ≠ 0 := by sorry
