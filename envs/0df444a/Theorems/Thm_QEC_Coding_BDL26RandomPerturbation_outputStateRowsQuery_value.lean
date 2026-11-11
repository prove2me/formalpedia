-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_outputStateRowsQuery_value
-- name    : QEC.Coding.BDL26RandomPerturbation.outputStateRowsQuery_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:57:49.125262+00:00
-- url     : https://prove2.me/theorems/4804599a-12d4-4e8c-b61f-2466f8d75621
-- title:
--   BDL26 Random Perturbation: output State Rows Query value
-- statement:
--   The actual emitted row list equals the perturbed map of the represented execution state.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateRows.lean#L168-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateRows.lean#L168-L182

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExecutionPrimitiveQueries
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateRows
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
variable {P : TannerSquarePresentation}

theorem QEC.Coding.BDL26RandomPerturbation.outputStateRowsQuery_value (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (T : Table (X := fun _ : Vertex P => Space)) (c : Counters (Vertex P))
    (R : StateRows P) (hR : StateRowsRep P T c R) :
    (outputStateRowsQuery P J lambda R).1 = (vertexInputList P).map
      (fun v => (v,lambda • ((1/2 : ℝ) • J v)+assignment T c v)) := by sorry
