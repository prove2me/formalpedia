-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeHamiltonianLocality_hamiltonianGeometry_of_physical
-- name    : QEC.Coding.BDL26NativeHamiltonianLocality.hamiltonianGeometry_of_physical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T11:56:01.836228+00:00
-- url     : https://prove2.me/theorems/2b83ca55-7f65-4f90-b244-ab708f8f43ae
-- title:
--   BDL26 Native Hamiltonian Locality: hamiltonian Geometry of physical
-- statement:
--   The BDL26 Native Hamiltonian Locality construction uses the hamiltonian Geometry of physical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeHamiltonianLocality.lean#L115-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeHamiltonianLocality.lean#L115-L125

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

theorem QEC.Coding.BDL26NativeHamiltonianLocality.hamiltonianGeometry_of_physical (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) {t : ℝ}
    (hJ : PhysicalGeometry S n J t) : HamiltonianGeometry S n J t := by sorry
