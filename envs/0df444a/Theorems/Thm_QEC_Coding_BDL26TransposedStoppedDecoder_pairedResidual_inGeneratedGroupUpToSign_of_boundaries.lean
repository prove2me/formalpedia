-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_pairedResidual_inGeneratedGroupUpToSign_of_boundaries
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.pairedResidual_inGeneratedGroupUpToSign_of_boundaries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:31:01.813402+00:00
-- url     : https://prove2.me/theorems/b08b301f-e5f1-445f-b8f5-5c425fd3686c
-- title:
--   BDL26 Transposed Stopped Decoder: paired Residual in Generated Group Up To Sign of boundaries
-- statement:
--   Ordinary actual row-boundary premises imply group membership up to sign.
--   The stored phase remains present and no exact generatedGroup conclusion is asserted.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L263-L272
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L263-L272

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.pairedResidual_inGeneratedGroupUpToSign_of_boundaries (S : OddScale) (n : Nat)
    (u : XSyndromeDomain S n) (v : ZSyndromeDomain S n) (E : Binary (Physical S (n + 2)))
    (hx : ∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a =
      (pairedResidual S n u v E).vector.xPart)
    (hz : ∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b =
      (pairedResidual S n u v E).vector.zPart) :
    (binaryCSSStabilizerCodeOfParityChecks (zSyndrome S (n + 2)) (xSyndrome S (n + 2))
      (row_orthogonal S (n + 2))).InGeneratedGroupUpToSign (pairedResidual S n u v E) := by sorry
