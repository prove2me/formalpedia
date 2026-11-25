-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_HypPairExists_hyps_7370eaa5e57f
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_HypPairExists_hyps_7370eaa5e57f
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:39:56.50344+00:00
-- url     : https://prove2.me/theorems/8facb95d-6508-466e-8aa5-900508284192
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Hyp Pair Exists hyps 7370eaa5e57f: P2 M Ground Theory Heights  Heights Strong Approx Hyp Pair Exists hyps 7370eaa5e57f
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Hyp Pair Exists hyps 7370eaa5e57f construction uses the P2 M Ground Theory Heights  Heights Strong Approx Hyp Pair Exists hyps 7370eaa5e57f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L444-L448
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L444-L448

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_HypPairExists_hyps_7370eaa5e57f :
    (∀ x, (conj ℚ GaussQ).toRingHom ((conj ℚ GaussQ).toRingHom x) = x) ∧ (2 : GaussQ) ≠ 0 ∧
      hypPlaneᵀ = hypPlane.map (conj ℚ GaussQ).toRingHom ∧ IsUnit hypPlane.det ∧ e0 ≠ 0 ∧
      hf (conj ℚ GaussQ).toRingHom hypPlane e0 e0 = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«HypPairExists».«hyps» := P2M_GroundTheory_Heights__Heights_StrongApprox_HypPairExists_hyps_7370eaa5e57f
