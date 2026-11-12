-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeHamiltonianLocality_checkSupport_subset_ball
-- name    : QEC.Coding.BDL26NativeHamiltonianLocality.checkSupport_subset_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:26:20.442728+00:00
-- url     : https://prove2.me/theorems/573cd950-98c4-4178-a652-816717fb40bb
-- title:
--   BDL26 Native Hamiltonian Locality: check Support subset ball
-- statement:
--   Containment is proved from actual check incidences and the same coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeHamiltonianLocality.lean#L59-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeHamiltonianLocality.lean#L59-L64

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

theorem QEC.Coding.BDL26NativeHamiltonianLocality.checkSupport_subset_ball (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) {t : ℝ}
    (hJ : PhysicalGeometry S n J t) (j : Sum (ZLabel S n) (XLabel S n)) :
    checkSupport S n j ⊆ (ballSubsystem S n J (checkCenter S n J j) 1).selected := by sorry
