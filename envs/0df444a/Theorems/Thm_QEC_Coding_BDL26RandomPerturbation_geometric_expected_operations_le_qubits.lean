-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometric_expected_operations_le_qubits
-- name    : QEC.Coding.BDL26RandomPerturbation.geometric_expected_operations_le_qubits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:14:54.278575+00:00
-- url     : https://prove2.me/theorems/3a4ac861-8021-4190-9c3f-4d88ed1ae9d9
-- title:
--   BDL26 Random Perturbation: geometric expected operations le qubits
-- statement:
--   All preprocessing and executed primitives are polynomial in the actual source qubit size.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExpectedOperationCost.lean#L146-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExpectedOperationCost.lean#L146-L165

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_capCutoff_bounds

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26RandomPerturbation.geometric_expected_operations_le_qubits (P : TannerSquarePresentation) (J : Vertex P → Space)
    (A : TannerSquareAdmissible P) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    letI (v : Vertex P) := vertexLaw_probability P
      ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
    (∫⁻ T, actualExecutionCost P J (by positivity : (0 : ℝ) ≤ anchorRadius p.m)
      p.lambda ((6*p.m+2)*p.lambda) T
      ∂tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))) ≤
        (operationConstant ((6*p.m+2)*p.lambda)*(65*Fintype.card P.Q+1)^10 : ℕ) := by sorry
