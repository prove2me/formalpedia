-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_pairedCorrection_phase
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.pairedCorrection_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:07:11.0302+00:00
-- url     : https://prove2.me/theorems/9e17fc5d-94ec-47c5-9b05-865a75cfbb3f
-- title:
--   BDL26 Transposed Stopped Decoder: paired Correction phase
-- statement:
--   The BDL26 Transposed Stopped Decoder construction uses the paired Correction phase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L196-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L196-L199

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.pairedCorrection_phase (S : OddScale) (n : Nat)
    (u : XSyndromeDomain S n) (v : ZSyndromeDomain S n) :
    (pairedCorrection S n u v).phase = 0 := by sorry
