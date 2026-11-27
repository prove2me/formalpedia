-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_SAOpenHolds_hyps_24f5835ce3b9
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_SAOpenHolds_hyps_24f5835ce3b9
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:44:24.266968+00:00
-- url     : https://prove2.me/theorems/810f51c8-3738-5cd4-940c-124da395c4c6
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx SAOpen Holds hyps 24f5835ce3b9: P2 M Ground Theory Heights  Heights Strong Approx SAOpen Holds hyps 24f5835ce3b9
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx SAOpen Holds hyps 24f5835ce3b9 construction uses the P2 M Ground Theory Heights  Heights Strong Approx SAOpen Holds hyps 24f5835ce3b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L538-L550
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L538-L550

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_LocGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_DenseRangeFiniteAdele
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open QuadraticAlgebra GroundTheory.Heights₂.Theta GroundTheory.Automorphic
attribute [local instance] topAE
attribute [local instance] isModuleTopology_AE

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_SAOpenHolds_hyps_24f5835ce3b9 :
    let Kg := SU (sigA (conj ℚ GaussQ)) (hypPlane.map (inclA ℚ GaussQ))
    Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧ hypPlaneᵀ = hypPlane.map (conj ℚ GaussQ) ∧
      IsUnit hypPlane.det ∧
      (∃ e : Fin 2 → GaussQ, e ≠ 0 ∧ hf (conj ℚ GaussQ).toRingHom hypPlane e e = 0) ∧
      IsModuleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AE ℚ GaussQ) ∧
      Kg ⊆ SU (sigA (conj ℚ GaussQ)) (hypPlane.map (inclA ℚ GaussQ)) ∧ 1 ∈ Kg ∧
      (∀ a ∈ Kg, ∀ b ∈ Kg, a * b ∈ Kg) ∧ (∀ a ∈ Kg, a⁻¹ ∈ Kg) ∧
      (∃ O, IsOpen O ∧ O ∩ SU (sigA (conj ℚ GaussQ)) (hypPlane.map (inclA ℚ GaussQ)) = Kg) ∧
      gA ∈ SU (sigA (conj ℚ GaussQ)) (hypPlane.map (inclA ℚ GaussQ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«SAOpenHolds».«hyps» := P2M_GroundTheory_Heights__Heights_StrongApprox_SAOpenHolds_hyps_24f5835ce3b9
