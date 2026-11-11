-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_monochromatic_triangle_hit_probability
-- name    : QEC.Coding.BDL26RandomPerturbation.monochromatic_triangle_hit_probability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:52:01.310493+00:00
-- url     : https://prove2.me/theorems/7a4bd59f-a392-42e3-9bc5-c16e8121912d
-- title:
--   BDL26 Random Perturbation: monochromatic triangle hit probability
-- statement:
--   A fixed ball is tested against every selected triangle; no pairwise-only shortcut.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Sampling.lean#L108-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Sampling.lean#L108-L134

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

theorem QEC.Coding.BDL26RandomPerturbation.monochromatic_triangle_hit_probability (P : TannerSquarePresentation)
    {A : Type*} [Fintype A] (labels : A → Triangle P) (hinj : Function.Injective labels)
    (hcolor : ∀ a b, triangleColor P (labels a) = triangleColor P (labels b))
    {R c ρ : ℝ} (hR : 0 < R) (hc0 : -1 < c) (hc1 : c < 1) (hρ : 0 ≤ ρ)
    (J : Vertex P → Space) (z : Space) :
    Measure.pi (vertexLaw P R c)
      {p | ∀ a, (fun i => p (triangleVertex P (labels a) i)) ∈
        triangleHit (fun i => J (triangleVertex P (labels a) i)) z ρ} ≤
      ENNReal.ofReal (18*ρ/(R*(1-c))) ^ Fintype.card A := by sorry
