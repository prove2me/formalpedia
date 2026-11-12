-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeDaviesLocality_daviesGeometry_of_physical
-- name    : QEC.Coding.BDL26NativeDaviesLocality.daviesGeometry_of_physical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:07:33.984705+00:00
-- url     : https://prove2.me/theorems/661f0e8d-10cd-49d7-a487-676565327fab
-- title:
--   BDL26 Native Davies Locality: davies Geometry of physical
-- statement:
--   The check-diameter facts yield radius2/diameter4 on the actual incident region;
--   existing operator theorems yield full-H support and canonical local restriction.
--   No support/geometry conclusion is assumed for any individual frequency or jump.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeDaviesLocality.lean#L134-L148
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeDaviesLocality.lean#L134-L148

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

theorem QEC.Coding.BDL26NativeDaviesLocality.daviesGeometry_of_physical (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) {t : ℝ}
    (hJ : PhysicalGeometry S n J t) : DaviesGeometry S n J t := by sorry
