-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_finite_cap_support
-- name    : QEC.Coding.BDL26RandomPerturbation.finite_cap_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:50:03.639344+00:00
-- url     : https://prove2.me/theorems/07804437-259d-426a-9487-af5e262d6121
-- title:
--   BDL26 Random Perturbation: finite cap support
-- statement:
--   The initial finite product is supported on the actual cap-valued assignments.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Sampling.lean#L26-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Sampling.lean#L26-L37

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

theorem QEC.Coding.BDL26RandomPerturbation.finite_cap_support (P : TannerSquarePresentation) {R c : ℝ} (hR : 0 < R)
    (hc : c < 1) :
    ∀ᵐ p ∂Measure.pi (vertexLaw P R c), ∀ v,
      p v ∈ displacementCap R (vertexAxis P v) c := by sorry
