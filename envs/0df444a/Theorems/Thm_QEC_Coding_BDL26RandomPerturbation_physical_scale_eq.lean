-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_physical_scale_eq
-- name    : QEC.Coding.BDL26RandomPerturbation.physical_scale_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:40:06.669205+00:00
-- url     : https://prove2.me/theorems/7d6240bc-692f-4db1-9167-2d3103585686
-- title:
--   BDL26 Random Perturbation: physical scale eq
-- statement:
--   Both canonical scales have exactly the same threshold, including odd rounding.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalSuccessor.lean#L25-L26
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalSuccessor.lean#L25-L26

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalSuccessor
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RXLocalReplacement
open BDL26RandomPhysicalLocality BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26CSSHamiltonian Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling MeasureTheory
variable {L : ℝ}

theorem QEC.Coding.BDL26RandomPerturbation.physical_scale_eq (p : GeometricParameters L) :
    replacementScale (6*(p.m : ℝ)) (p.lambda : ℝ) p.rounding = perturbationOddScale p := by sorry
