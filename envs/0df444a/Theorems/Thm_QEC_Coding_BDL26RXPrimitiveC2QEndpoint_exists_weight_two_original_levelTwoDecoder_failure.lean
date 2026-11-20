-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPrimitiveC2QEndpoint_exists_weight_two_original_levelTwoDecoder_failure
-- name    : QEC.Coding.BDL26RXPrimitiveC2QEndpoint.exists_weight_two_original_levelTwoDecoder_failure
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T12:40:25.226935+00:00
-- url     : https://prove2.me/theorems/e27b4a53-05ec-49da-8a07-4871f11530b6
-- title:
--   BDL26 RXPrimitive C2 QEndpoint: exists weight two original level Two Decoder failure
-- statement:
--   At every OddScale the current specific canonical base lookup has an actual
--   weight-two Physical S 2 error with a valid actual syndrome whose complete
--   original error-plus-decoding residual is closed and is not an actual boundary.
--   This is a statement about this implementation, not a paper radius-two decoder
--   contract, a distance lower bound, or a counterexample to a paper theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18548-L18562
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18548-L18562

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint
set_option autoImplicit false
noncomputable section
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph

theorem QEC.Coding.BDL26RXPrimitiveC2QEndpoint.exists_weight_two_original_levelTwoDecoder_failure (S : OddScale) :
    ∃ e : Word BDL26Field (BDL26CSSHamiltonian.Physical S 2),
      HammingWeight e=2 ∧
      BDL26CSSHamiltonian.zSyndrome S 2 e ∈
        LinearMap.range (BDL26CSSHamiltonian.zSyndrome S 2) ∧
      let residual : Word BDL26Field (BDL26CSSHamiltonian.Physical S 2) :=
        e+(fun q : BDL26CSSHamiltonian.Physical S 2 =>
          BDL26LevelTwoDecoder.decode S (BDL26CSSHamiltonian.zSyndrome S 2 e) q)
      BDL26CSSHamiltonian.zSyndrome S 2 residual=0 ∧
        residual ∉ LinearMap.range
          (QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary0 (BDL26DecodingGraph.state S 2).presentation) := by sorry
