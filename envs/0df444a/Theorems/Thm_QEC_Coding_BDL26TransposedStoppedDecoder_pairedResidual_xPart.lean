-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_pairedResidual_xPart
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.pairedResidual_xPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:11:44.425205+00:00
-- url     : https://prove2.me/theorems/0e85bd44-be9d-4c37-b8e1-1a393ff7da3e
-- title:
--   BDL26 Transposed Stopped Decoder: paired Residual x Part
-- statement:
--   Full X residual, including both independently computed background corrections.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L216-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L216-L220

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.pairedResidual_xPart (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (v : ZSyndromeDomain S n) (E : Binary (Physical S (n + 2))) :
    (pairedResidual S n u v E).vector.xPart =
      xCorrection S n (translateX S n u E.vector.xPart) + E.vector.xPart + xCorrection S n u := by sorry
