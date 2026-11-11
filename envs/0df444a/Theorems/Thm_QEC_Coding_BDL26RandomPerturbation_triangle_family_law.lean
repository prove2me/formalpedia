-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangle_family_law
-- name    : QEC.Coding.BDL26RandomPerturbation.triangle_family_law
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:51:18.102205+00:00
-- url     : https://prove2.me/theorems/81410622-9648-4084-b516-f3249cb998cb
-- title:
--   BDL26 Random Perturbation: triangle family law
-- statement:
--   Reindexing the actual vertex product derives a joint product of triangle laws.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Sampling.lean#L84-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Sampling.lean#L84-L105

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

theorem QEC.Coding.BDL26RandomPerturbation.triangle_family_law (P : TannerSquarePresentation) {A : Type*} [Fintype A]
    (labels : A → Triangle P) (hinj : Function.Injective labels)
    (hcolor : ∀ a b, triangleColor P (labels a) = triangleColor P (labels b))
    (ν : Vertex P → Measure Space) [∀ v, IsProbabilityMeasure (ν v)] :
    (Measure.pi ν).map (fun p a i => p (triangleVertex P (labels a) i)) =
      Measure.pi (fun a => Measure.pi (fun i => ν (triangleVertex P (labels a) i))) := by sorry
