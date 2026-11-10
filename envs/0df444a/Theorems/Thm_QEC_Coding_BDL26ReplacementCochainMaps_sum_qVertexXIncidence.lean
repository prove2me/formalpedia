-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_sum_qVertexXIncidence
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.sum_qVertexXIncidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:19:10.649202+00:00
-- url     : https://prove2.me/theorems/c3db178e-b87f-4231-a1f9-01e7ecd2772b
-- title:
--   BDL26 Replacement Cochain Maps: sum q Vertex XIncidence
-- statement:
--   The BDL26 Replacement Cochain Maps construction uses the sum q Vertex XIncidence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L334-L350
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L334-L350

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

theorem QEC.Coding.BDL26ReplacementCochainMaps.sum_qVertexXIncidence
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale)
    (x : P.X) (q : P.Q) (qVertex : QDoubleCylinderVertex P q S) :
    (∑ xVertex : DoubleCylinderVertex P x S,
      qDoubleCylinderVertexXIncidence P q x S xVertex qVertex) =
        if P.xq x q = true then 1 else 0 := by sorry
