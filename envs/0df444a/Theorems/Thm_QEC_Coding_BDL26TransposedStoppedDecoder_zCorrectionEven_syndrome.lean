-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_zCorrectionEven_syndrome
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.zCorrectionEven_syndrome
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T17:23:34.200214+00:00
-- url     : https://prove2.me/theorems/703ac5fd-eddf-4bc5-bca1-5fc336451f06
-- title:
--   BDL26 Transposed Stopped Decoder: z Correction Even syndrome
-- statement:
--   The source-even wrapper has the literal physical syndrome for every k>=1.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L290-L294
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L290-L294

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.zCorrectionEven_syndrome (S : OddScale) (k : Nat) (hk : 1 ≤ k)
    (v : LinearMap.range (xSyndrome S (2 * k))) :
    xSyndrome S (2 * k) (zCorrectionEven S k hk v) = v.val := by sorry
