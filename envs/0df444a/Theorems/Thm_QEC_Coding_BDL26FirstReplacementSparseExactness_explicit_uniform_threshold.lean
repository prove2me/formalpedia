-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_explicit_uniform_threshold
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.explicit_uniform_threshold
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T10:52:48.850708+00:00
-- url     : https://prove2.me/theorems/0a779a05-c0df-46be-b841-d22bafeff8c2
-- title:
--   BDL26 First Replacement Sparse Exactness: explicit uniform threshold
-- statement:
--   The BDL26 First Replacement Sparse Exactness construction uses the explicit uniform threshold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L407-L413
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L407-L413

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstReplacementSparseExactness
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.explicit_uniform_threshold :
    ∃ H : Nat, ∀ S : OddScale, H≤S.half →
      ∀ w : Word Bit (BDL26DecodingGraph.state S 1).presentation.Q,
        tannerCoboundary1 (BDL26DecodingGraph.state S 1).presentation w=0 →
        HammingWeight w≤14 →
        w ∈ LinearMap.range (tannerCoboundary0 (BDL26DecodingGraph.state S 1).presentation) := by sorry
