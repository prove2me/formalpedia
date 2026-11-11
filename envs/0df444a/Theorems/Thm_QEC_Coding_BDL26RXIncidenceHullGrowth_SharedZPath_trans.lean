-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_SharedZPath_trans
-- name    : QEC.Coding.BDL26RXIncidenceHullGrowth.SharedZPath.trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:39:01.005908+00:00
-- url     : https://prove2.me/theorems/a711d2d7-3e3c-41ff-8d7d-8251974a377c
-- title:
--   Shared ZPath: trans
-- statement:
--   The Shared ZPath construction uses the trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGrowth.lean#L24-L28
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGrowth.lean#L24-L28

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGrowth
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26RXDifferentialMasks
open BDL26FiniteAlternatingCore MultiscaleDecoder BDL26IndexedDecoder

theorem QEC.Coding.BDL26RXIncidenceHullGrowth.SharedZPath.trans {P : TannerSquarePresentation} {q r t : P.Q}
    (first : SharedZPath P q r) (second : SharedZPath P r t) : SharedZPath P q t := by sorry
