-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_monochromatic_addresses_injective
-- name    : QEC.Coding.BDL26RandomPerturbation.monochromatic_addresses_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:51:02.486559+00:00
-- url     : https://prove2.me/theorems/8fcb38a6-562e-4480-b355-37504233be8e
-- title:
--   BDL26 Random Perturbation: monochromatic addresses injective
-- statement:
--   Joint address injectivity follows from the proved incidence-rank coloring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Sampling.lean#L68-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Sampling.lean#L68-L81

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

theorem QEC.Coding.BDL26RandomPerturbation.monochromatic_addresses_injective (P : TannerSquarePresentation)
    {A : Type*} (labels : A → Triangle P) (hinj : Function.Injective labels)
    (hcolor : ∀ a b, triangleColor P (labels a) = triangleColor P (labels b)) :
    Function.Injective (fun s : (a : A) × Fin 3 => triangleVertex P (labels s.1) s.2) := by sorry
