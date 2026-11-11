-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometric_scan_value
-- name    : QEC.Coding.BDL26RandomPerturbation.geometric_scan_value
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T00:18:45.625199+00:00
-- url     : https://prove2.me/theorems/2d36d9f1-5c6e-4e5b-8211-d0dab32912ce
-- title:
--   BDL26 Random Perturbation: geometric scan value
-- statement:
--   The BDL26 Random Perturbation construction uses the geometric scan value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedScan.lean#L59-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedScan.lean#L59-L64

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Cost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedScan
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26RandomPerturbation.geometric_scan_value (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (p : Vertex P → Space) :
    (scanQuery (geometricGlobalQuery P J r lambda K)
      ((Finset.univ : Finset (Event P J r)).sort (eventPriorityLE P J r)) p).1 =
      select (localEvent (X := fun _ : Vertex P => Space) (eventSupport P J r) (eventBad P J r lambda K)) p := by sorry
