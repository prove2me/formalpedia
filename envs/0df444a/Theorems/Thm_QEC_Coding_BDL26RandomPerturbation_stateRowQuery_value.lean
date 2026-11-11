-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_stateRowQuery_value
-- name    : QEC.Coding.BDL26RandomPerturbation.stateRowQuery_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:53:55.081969+00:00
-- url     : https://prove2.me/theorems/3cc7f6b1-937b-46a5-aa88-9c4bd7f34ffc
-- title:
--   BDL26 Random Perturbation: state Row Query value
-- statement:
--   The BDL26 Random Perturbation construction uses the state Row Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateRows.lean#L39-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateRows.lean#L39-L54

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExecutionPrimitiveQueries
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateRows
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
variable {P : TannerSquarePresentation}

theorem QEC.Coding.BDL26RandomPerturbation.stateRowQuery_value (v : Vertex P) (R : StateRows P) (x : ℕ × Space)
    (hrows : ∀ row ∈ R, row.1=v → row.2=x) (hmem : ∃ row ∈ R, row.1=v) :
    (stateRowQuery v R).1 = x := by sorry
