-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeHamiltonianLocality_signedCheck_supported_ball
-- name    : QEC.Coding.BDL26NativeHamiltonianLocality.signedCheck_supported_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:27:00.256145+00:00
-- url     : https://prove2.me/theorems/3f9c105a-bb93-44b9-ad6f-6331b7b6ae8e
-- title:
--   BDL26 Native Hamiltonian Locality: signed Check supported ball
-- statement:
--   Genuine tensor identity-extension support, rather than a metric-only assertion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeHamiltonianLocality.lean#L67-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeHamiltonianLocality.lean#L67-L76

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

theorem QEC.Coding.BDL26NativeHamiltonianLocality.signedCheck_supported_ball (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) {t : ℝ}
    (hJ : PhysicalGeometry S n J t) (j : Sum (ZLabel S n) (XLabel S n)) :
    (ballSubsystem S n J (checkCenter S n J j) 1).OperatorSupportedOnRegister
      (signedCheck S n j) := by sorry
