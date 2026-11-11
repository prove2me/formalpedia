-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_StateRowsRep_length
-- name    : QEC.Coding.BDL26RandomPerturbation.StateRowsRep_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:54:38.785884+00:00
-- url     : https://prove2.me/theorems/7211dac9-4842-4ff8-b81e-48c07c3477dd
-- title:
--   BDL26 Random Perturbation: State Rows Rep length
-- statement:
--   The BDL26 Random Perturbation construction uses the State Rows Rep length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateRows.lean#L56-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateRows.lean#L56-L60

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExecutionPrimitiveQueries
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateRows
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
variable {P : TannerSquarePresentation}

theorem QEC.Coding.BDL26RandomPerturbation.StateRowsRep_length (P : TannerSquarePresentation) (T : Table (X := fun _ : Vertex P => Space))
    (c : Counters (Vertex P)) (R : StateRows P) (hR : StateRowsRep P T c R) :
    R.length = Fintype.card (Vertex P) := by sorry
