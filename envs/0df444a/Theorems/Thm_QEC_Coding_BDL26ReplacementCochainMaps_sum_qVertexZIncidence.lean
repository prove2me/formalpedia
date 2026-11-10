-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_sum_qVertexZIncidence
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.sum_qVertexZIncidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:38:59.226882+00:00
-- url     : https://prove2.me/theorems/28bbdbbb-60ec-40a1-98f5-350aac664022
-- title:
--   BDL26 Replacement Cochain Maps: sum q Vertex ZIncidence
-- statement:
--   The BDL26 Replacement Cochain Maps construction uses the sum q Vertex ZIncidence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L380-L394
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L380-L394

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementCochainMaps
open scoped BigOperators Classical
open QEC.Coding
open QEC.Coding.BDL26FiniteTannerSquare
open QEC.Coding.BDL26TannerLocalRegularity
open QEC.Coding.BDL26RXLocalReplacement
open QEC.Coding.BDL26RZLocalReplacement
open QEC.Coding.BDL26RZMap1CoordinateBridge
open QEC.Coding.MultiscaleDecoder

theorem QEC.Coding.BDL26ReplacementCochainMaps.sum_qVertexZIncidence
    (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) (z : P.Z) (copy : Two) :
    (∑ vertex : QDoubleCylinderVertex P q S,
      qDoubleCylinderVertexZIncidence P q S vertex (z, copy)) =
        if P.qz q z = true then 1 else 0 := by sorry
