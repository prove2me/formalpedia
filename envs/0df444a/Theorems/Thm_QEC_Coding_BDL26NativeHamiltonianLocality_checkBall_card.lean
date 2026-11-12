-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeHamiltonianLocality_checkBall_card
-- name    : QEC.Coding.BDL26NativeHamiltonianLocality.checkBall_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:27:27.661963+00:00
-- url     : https://prove2.me/theorems/a1d14330-2435-4b22-99b6-b7ebd6a3f9b7
-- title:
--   BDL26 Native Hamiltonian Locality: check Ball card
-- statement:
--   The BDL26 Native Hamiltonian Locality construction uses the check Ball card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeHamiltonianLocality.lean#L92-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeHamiltonianLocality.lean#L92-L96

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

theorem QEC.Coding.BDL26NativeHamiltonianLocality.checkBall_card (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) {t : ℝ}
    (hJ : PhysicalGeometry S n J t) (j : Sum (ZLabel S n) (XLabel S n)) :
    (((ballSubsystem S n J (checkCenter S n J j) 1).selected.card : ℕ) : ℝ) ≤ 2*t := by sorry
