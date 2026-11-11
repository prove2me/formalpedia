-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_rz_map2_weight
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.rz_map2_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:33:01.154123+00:00
-- url     : https://prove2.me/theorems/9a0ca1a2-7b11-4abd-99a1-a346dd1959cd
-- title:
--   BDL26 Uniform History Obstruction: rz map2 weight
-- statement:
--   RZ map2 preserves the global Hamming weight of every word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L79-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L79-L85

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26UniformHistoryObstruction.rz_map2_weight (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (s : Word BDL26Field P.Z) :
    HammingWeight (map2Coord P A S s) = HammingWeight s := by sorry
