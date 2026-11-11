-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_face_arm
-- name    : QEC.Coding.BDL26FirstReplacementSparseExactness.face_arm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:13:14.879838+00:00
-- url     : https://prove2.me/theorems/2bdf8465-9b1e-4251-8876-df64f4330a88
-- title:
--   BDL26 First Replacement Sparse Exactness: face arm
-- statement:
--   The BDL26 First Replacement Sparse Exactness construction uses the face arm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L85-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L85-L88

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

theorem QEC.Coding.BDL26FirstReplacementSparseExactness.face_arm (b : Fin 2) :
    (xStarFaceQZEdge Seed center (oldFace b) 0).val =
      Sum.inr ⟨(oldQ b,b), (armEdge b).property⟩ := by sorry
