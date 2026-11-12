-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeHamiltonianLocality_measurableSet_finiteHamiltonianSuccess
-- name    : QEC.Coding.BDL26NativeHamiltonianLocality.measurableSet_finiteHamiltonianSuccess
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:44:07.642507+00:00
-- url     : https://prove2.me/theorems/fae2b375-f1c1-4875-8ed4-037154e27604
-- title:
--   BDL26 Native Hamiltonian Locality: measurable Set finite Hamiltonian Success
-- statement:
--   The BDL26 Native Hamiltonian Locality construction uses the measurable Set finite Hamiltonian Success property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeHamiltonianLocality.lean#L159-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeHamiltonianLocality.lean#L159-L162

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeHamiltonianLocality
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open PauliSymplectic Semantics
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26NativeHamiltonianLocality.measurableSet_finiteHamiltonianSuccess {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    MeasurableSet (finiteHamiltonianSuccess p N) := by sorry
