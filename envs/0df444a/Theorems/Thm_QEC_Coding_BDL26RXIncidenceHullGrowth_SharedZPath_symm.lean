-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_SharedZPath_symm
-- name    : QEC.Coding.BDL26RXIncidenceHullGrowth.SharedZPath.symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:40:15.365043+00:00
-- url     : https://prove2.me/theorems/0180ec67-0f1f-40ec-a598-bb19e40a9cd0
-- title:
--   Shared ZPath: symm
-- statement:
--   The Shared ZPath construction uses the symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGrowth.lean#L30-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGrowth.lean#L30-L35

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGrowth
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26RXDifferentialMasks
open BDL26FiniteAlternatingCore MultiscaleDecoder BDL26IndexedDecoder

theorem QEC.Coding.BDL26RXIncidenceHullGrowth.SharedZPath.symm {P : TannerSquarePresentation} {q r : P.Q}
    (path : SharedZPath P q r) : SharedZPath P r q := by sorry
