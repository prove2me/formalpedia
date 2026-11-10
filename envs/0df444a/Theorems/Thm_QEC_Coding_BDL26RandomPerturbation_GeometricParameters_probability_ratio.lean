-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_GeometricParameters_probability_ratio
-- name    : QEC.Coding.BDL26RandomPerturbation.GeometricParameters.probability_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:10:09.3702+00:00
-- url     : https://prove2.me/theorems/d0a83a87-57c4-4fab-b5b8-eea3690a6301
-- title:
--   Geometric Parameters: probability ratio
-- statement:
--   The Geometric Parameters construction uses the probability ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ConcreteParameters.lean#L65-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ConcreteParameters.lean#L65-L73

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ProbabilityDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_DependencyCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LLLCriterion
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ConcreteParameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.GeometricParameters.probability_ratio {densityLower : ℝ}
    (p : GeometricParameters densityLower) :
    probabilityCoefficient (6*p.m) (capCutoff p.m)/(p.lambda : ℝ) ≤
      1/(4*((dependencyBound p.M : ℝ)+1)) := by sorry
