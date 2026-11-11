-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_assignment_cap_support
-- name    : QEC.Coding.BDL26RandomPerturbation.assignment_cap_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:53:58.833336+00:00
-- url     : https://prove2.me/theorems/a890ea18-f15d-44a1-a3b3-60b40c86bb1f
-- title:
--   BDL26 Random Perturbation: assignment cap support
-- statement:
--   The full-table event suffices for arbitrary counters, including data-dependent ones.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Sampling.lean#L57-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Sampling.lean#L57-L65

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Coloring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_TriangleHit
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Sampling
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory

theorem QEC.Coding.BDL26RandomPerturbation.assignment_cap_support (P : TannerSquarePresentation) {R c : ℝ} (hR : 0 < R)
    (hc : c < 1) :
    letI (v : Vertex P) := vertexLaw_probability P R hc v
    ∀ᵐ T ∂tableLaw (vertexLaw P R c), ∀ n : Vertex P → ℕ, ∀ v : Vertex P,
      assignment T n v ∈ displacementCap R (vertexAxis P v) c := by sorry
