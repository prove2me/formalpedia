-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_stampRowsQuery_value
-- name    : QEC.Coding.BDL26PaidRowsComposition.stampRowsQuery_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:29:46.469479+00:00
-- url     : https://prove2.me/theorems/01a7e727-39a2-450f-82f5-0d0c9779a1db
-- title:
--   BDL26 Paid Rows Composition: stamp Rows Query value
-- statement:
--   The BDL26 Paid Rows Composition construction uses the stamp Rows Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L32-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L32-L34

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PaidRowsComposition
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26ReplacementMaterialization BDL26IncomingRowsExecution
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26PaidRowsComposition.stampRowsQuery_value {A : Type*} (R : List (A × Space)) :
    (stampRowsQuery R).1 = R.map (fun row => (row.1,0,row.2)) := by sorry
