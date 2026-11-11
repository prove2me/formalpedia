-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_lookup_zero_of_zero_first
-- name    : QEC.Coding.BDL26LevelTwoDecoder.lookup_zero_of_zero_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:15:31.320391+00:00
-- url     : https://prove2.me/theorems/e2f286b4-d0f3-4b75-b1a5-a665ec9ede62
-- title:
--   BDL26 Level Two Decoder: lookup zero of zero first
-- statement:
--   A local zero head is chosen by the first, local-only search.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDecoderZero.lean#L41-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDecoderZero.lean#L41-L48

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDecoder
open BDL26FiniteTannerSquare BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26TannerLocalRegularity BDL26RZMap1CoordinateBridge
open MultiscaleDecoder

theorem QEC.Coding.BDL26LevelTwoDecoder.lookup_zero_of_zero_first {Error Syndrome : Type} [Zero Error]
    [Zero Syndrome] [DecidableEq Syndrome] (entries : List Error)
    (syndrome : Error → Syndrome) (isLocal : Error → Bool) (fallback : Error)
    (hfirst : ∃ tail, entries = 0 :: tail) (hlocal : isLocal 0 = true)
    (hsyndrome : syndrome 0 = 0) :
    lookup entries syndrome isLocal fallback 0 = 0 := by sorry
