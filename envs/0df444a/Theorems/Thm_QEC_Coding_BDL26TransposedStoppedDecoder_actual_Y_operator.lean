-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_actual_Y_operator
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.actual_Y_operator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:30:24.532761+00:00
-- url     : https://prove2.me/theorems/de39092e-dd22-43bf-a442-22684d96d48e
-- title:
--   BDL26 Transposed Stopped Decoder: actual Y operator
-- statement:
--   Actual Y changes both sectors. Its Hermitian operator retains i*(X*Z).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L275-L278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L275-L278

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.actual_Y_operator (S : OddScale) (n : Nat) (q : Physical S (n + 2)) :
    CSSDaviesLocality.coupling q .y = Complex.I •
      (Semantics.Qubit.localX q * Semantics.Qubit.localZ q) := by sorry
