-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_pairedResidual_zPart
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.pairedResidual_zPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:08:46.686374+00:00
-- url     : https://prove2.me/theorems/5ac91df1-ce78-444e-b3ca-f4a326a8aebd
-- title:
--   BDL26 Transposed Stopped Decoder: paired Residual z Part
-- statement:
--   Full Z residual on that very same physical carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L223-L227
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L223-L227

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.pairedResidual_zPart (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (v : ZSyndromeDomain S n) (E : Binary (Physical S (n + 2))) :
    (pairedResidual S n u v E).vector.zPart =
      zCorrection S n (translateZ S n v E.vector.zPart) + E.vector.zPart + zCorrection S n v := by sorry
