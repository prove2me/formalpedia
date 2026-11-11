-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_zCorrection_syndrome
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.zCorrection_syndrome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:07:25.437224+00:00
-- url     : https://prove2.me/theorems/12b58a12-12cd-4461-8e75-712d6bd49054
-- title:
--   BDL26 Transposed Stopped Decoder: z Correction syndrome
-- statement:
--   Same physical carrier and literal original X-check syndrome, for every n>=0.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L130-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L130-L143

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.zCorrection_syndrome (S : OddScale) (n : Nat) (v : ZSyndromeDomain S n) :
    xSyndrome S (n + 2) (zCorrection S n v) = v.val := by sorry
