-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_actualPrefixQuery_rep
-- name    : QEC.Coding.BDL26RandomPerturbation.actualPrefixQuery_rep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:04:10.527959+00:00
-- url     : https://prove2.me/theorems/39a3aafe-7d63-42d5-9b13-f2ccfc8d9b83
-- title:
--   BDL26 Random Perturbation: actual Prefix Query rep
-- statement:
--   The exact stored counter and sample address agree with core1447 at every finite prefix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ActualExecutionCost.lean#L111-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ActualExecutionCost.lean#L111-L119

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateEventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventPreprocessingCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26RandomPerturbation.actualPrefixQuery_rep (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space)) (n : ℕ) :
    StateRowsRep P T (counters (eventSupport P J r) (eventBad P J r lambda K) T n)
      (actualPrefixQuery P J r lambda K (eventUniverseQuery P J hr).1 T n).1 := by sorry
