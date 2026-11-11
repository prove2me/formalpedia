-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_operation_input_size_le_qubits
-- name    : QEC.Coding.BDL26RandomPerturbation.operation_input_size_le_qubits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:10:32.673203+00:00
-- url     : https://prove2.me/theorems/1de02a0e-2ca3-43c0-97c0-2ef8f01cc058
-- title:
--   BDL26 Random Perturbation: operation input size le qubits
-- statement:
--   Genuine admissibility roots and incidence bounds control both source input arrays.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExpectedOperationCost.lean#L77-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExpectedOperationCost.lean#L77-L80

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26RandomPerturbation.operation_input_size_le_qubits (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (hv : BoundedValence P) : Fintype.card (Vertex P)+Fintype.card (Triangle P) ≤ 65*Fintype.card P.Q := by sorry
