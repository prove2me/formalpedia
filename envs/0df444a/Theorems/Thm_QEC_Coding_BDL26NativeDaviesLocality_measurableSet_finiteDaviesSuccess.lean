-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeDaviesLocality_measurableSet_finiteDaviesSuccess
-- name    : QEC.Coding.BDL26NativeDaviesLocality.measurableSet_finiteDaviesSuccess
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:49:56.211618+00:00
-- url     : https://prove2.me/theorems/c411e1cb-7956-4ad7-92d0-b129d12c2cad
-- title:
--   BDL26 Native Davies Locality: measurable Set finite Davies Success
-- statement:
--   The BDL26 Native Davies Locality construction uses the measurable Set finite Davies Success property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeDaviesLocality.lean#L180-L183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeDaviesLocality.lean#L180-L183

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeDaviesLocality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeDaviesLocality
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open BDL26CSSDaviesLocality
open PauliSymplectic Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26NativeDaviesLocality.measurableSet_finiteDaviesSuccess {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    MeasurableSet (finiteDaviesSuccess p N) := by sorry
