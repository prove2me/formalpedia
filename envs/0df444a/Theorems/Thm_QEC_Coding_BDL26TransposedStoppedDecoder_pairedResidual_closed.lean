-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_pairedResidual_closed
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.pairedResidual_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:11:34.153417+00:00
-- url     : https://prove2.me/theorems/84a3e47f-c7c3-4579-aa26-8d4468c4b1c8
-- title:
--   BDL26 Transposed Stopped Decoder: paired Residual closed
-- statement:
--   Correctness proves both residuals closed; it does not prove either is a boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L239-L259
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L239-L259

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.pairedResidual_closed (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (v : ZSyndromeDomain S n) (E : Binary (Physical S (n + 2))) :
    zSyndrome S (n + 2) (pairedResidual S n u v E).vector.xPart = 0 ∧
    xSyndrome S (n + 2) (pairedResidual S n u v E).vector.zPart = 0 := by sorry
