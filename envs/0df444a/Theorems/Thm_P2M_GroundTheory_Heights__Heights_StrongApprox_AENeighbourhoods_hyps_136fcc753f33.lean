-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_hyps_136fcc753f33
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_hyps_136fcc753f33
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:39:18.153322+00:00
-- url     : https://prove2.me/theorems/8a9772bd-30d6-47a1-8a25-bc8d0d2c3b32
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods hyps 136fcc753f33: P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods hyps 136fcc753f33
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods hyps 136fcc753f33 construction uses the P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods hyps 136fcc753f33 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L513-L517
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L513-L517

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_hyps_136fcc753f33 :
    Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧
      IsModuleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AE ℚ GaussQ) ∧
      (Set.univ : Set (Matrix (Fin 2) (Fin 2) (AE ℚ GaussQ))) ∈ 𝓝 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«AENeighbourhoods».«hyps» := P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_hyps_136fcc753f33
