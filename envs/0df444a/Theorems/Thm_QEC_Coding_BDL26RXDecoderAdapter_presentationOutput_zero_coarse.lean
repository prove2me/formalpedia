-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_presentationOutput_zero_coarse
-- name    : QEC.Coding.BDL26RXDecoderAdapter.presentationOutput_zero_coarse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:09:19.27178+00:00
-- url     : https://prove2.me/theorems/148ba257-edcd-43ea-bbea-938f7ac89e5a
-- title:
--   BDL26 RXDecoder Adapter: presentation Output zero coarse
-- statement:
--   Zero coarse syndrome follows from the actual factor-two bound. The chosen
--   zero-run correction is retained and need not itself be zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L1493-L1502
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L1493-L1502

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Representative
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Graph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Sectors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Induced
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Budgets
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_LocalComplexes
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData

theorem QEC.Coding.BDL26RXDecoderAdapter.presentationOutput_zero_coarse (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (sigma : (presentationFamily P A R S).Syndrome (1 : LevelIndex 1))
    (hs : sigma.val = 0) : (presentationOutput P A R S sigma).coarse.val = 0 := by sorry
