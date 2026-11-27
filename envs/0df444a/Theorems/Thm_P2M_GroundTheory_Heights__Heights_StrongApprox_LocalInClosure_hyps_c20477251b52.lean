-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_LocalInClosure_hyps_c20477251b52
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_LocalInClosure_hyps_c20477251b52
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:39:48.26439+00:00
-- url     : https://prove2.me/theorems/9fc1422b-b92b-4af0-8e39-32edfcad798b
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Local In Closure hyps c20477251b52: P2 M Ground Theory Heights  Heights Strong Approx Local In Closure hyps c20477251b52
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Local In Closure hyps c20477251b52 construction uses the P2 M Ground Theory Heights  Heights Strong Approx Local In Closure hyps c20477251b52 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L504-L511
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L504-L511

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_LocalInClosure_hyps_c20477251b52 :
    Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧ hypPlaneᵀ = hypPlane.map (conj ℚ GaussQ) ∧
      IsUnit hypPlane.det ∧
      (∃ e : Fin 2 → GaussQ, e ≠ 0 ∧ hf (conj ℚ GaussQ).toRingHom hypPlane e e = 0) ∧
      IsModuleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AE ℚ GaussQ) ∧
      g5 ∈ SU (sigV (conj ℚ GaussQ) v5).toRingHom (hypPlane.map (inclV GaussQ v5)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«LocalInClosure».«hyps» := P2M_GroundTheory_Heights__Heights_StrongApprox_LocalInClosure_hyps_c20477251b52
