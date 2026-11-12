-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_stampRowsQuery_read
-- name    : QEC.Coding.BDL26PaidRowsComposition.stampRowsQuery_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:32:32.382231+00:00
-- url     : https://prove2.me/theorems/e19a3cfe-9b7c-493e-a13f-4b70a79ea787
-- title:
--   BDL26 Paid Rows Composition: stamp Rows Query read
-- statement:
--   Equality includes actual first-match lookup costs, missing labels and duplicates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L51-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L51-L62

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

theorem QEC.Coding.BDL26PaidRowsComposition.stampRowsQuery_read (P : TannerSquarePresentation)
    (R : List (Vertex P × Space)) (v : Vertex P) :
    incomingRead P (stampRowsQuery R).1 v = pointRowQuery v R := by sorry
