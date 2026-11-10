-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_capCutoff_bounds
-- name    : QEC.Coding.BDL26RandomPerturbation.capCutoff_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:06:24.366226+00:00
-- url     : https://prove2.me/theorems/4c8f21e6-007d-49e0-bc4f-05d53990ebe3
-- title:
--   BDL26 Random Perturbation: cap Cutoff bounds
-- statement:
--   The BDL26 Random Perturbation construction uses the cap Cutoff bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ConcreteParameters.lean#L55-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ConcreteParameters.lean#L55-L63

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ProbabilityDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_DependencyCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LLLCriterion
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ConcreteParameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.capCutoff_bounds {m : ℕ} (hm : 2 ≤ m) :
    -1 < capCutoff m ∧ capCutoff m < 1 := by sorry
