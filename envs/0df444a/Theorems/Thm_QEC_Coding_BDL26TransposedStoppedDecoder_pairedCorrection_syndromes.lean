-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_pairedCorrection_syndromes
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.pairedCorrection_syndromes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:11:16.796404+00:00
-- url     : https://prove2.me/theorems/07641927-f04b-4f13-8524-fe5efd119261
-- title:
--   BDL26 Transposed Stopped Decoder: paired Correction syndromes
-- statement:
--   Both actual syndrome coordinates, without an abstract output chooser.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L202-L207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L202-L207

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.pairedCorrection_syndromes (S : OddScale) (n : Nat)
    (u : XSyndromeDomain S n) (v : ZSyndromeDomain S n) :
    zSyndrome S (n + 2) (pairedCorrection S n u v).vector.xPart = u.val ∧
    xSyndrome S (n + 2) (pairedCorrection S n u v).vector.zPart = v.val := by sorry
