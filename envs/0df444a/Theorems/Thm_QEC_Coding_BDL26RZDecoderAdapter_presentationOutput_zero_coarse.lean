-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_presentationOutput_zero_coarse
-- name    : QEC.Coding.BDL26RZDecoderAdapter.presentationOutput_zero_coarse
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:58:14.446285+00:00
-- url     : https://prove2.me/theorems/66028b77-ae03-4c82-ae22-7ee36b6b391b
-- title:
--   BDL26 RZDecoder Adapter: presentation Output zero coarse
-- statement:
--   Actual parity aggregation sends zero input to zero coarse syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean#L767-L773
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean#L767-L773

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZSupportedBoundary
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity MultiscaleDecoder
open RZCoarseGraining RZCoarseGrainingData

theorem QEC.Coding.BDL26RZDecoderAdapter.presentationOutput_zero_coarse (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale)
    (sigma : (presentationFamily P A S).Syndrome (1 : LevelIndex 1))
    (hs : sigma.val = 0) : (presentationOutput P A S sigma).coarse.val = 0 := by sorry
