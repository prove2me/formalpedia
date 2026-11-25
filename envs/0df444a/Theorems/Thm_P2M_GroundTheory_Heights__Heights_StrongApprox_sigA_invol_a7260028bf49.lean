-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_sigA_invol_a7260028bf49
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_sigA_invol_a7260028bf49
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:41:18.971855+00:00
-- url     : https://prove2.me/theorems/793933e8-c9c4-4ac4-9cb8-66a0a922ea20
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx sig A invol a7260028bf49: P2 M Ground Theory Heights  Heights Strong Approx sig A invol a7260028bf49
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx sig A invol a7260028bf49 construction uses the P2 M Ground Theory Heights  Heights Strong Approx sig A invol a7260028bf49 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L344-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L344-L348

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_sigA_invol_a7260028bf49 (x : AE ℚ GaussQ) : sigA (conj ℚ GaussQ) (sigA (conj ℚ GaussQ) x) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«sigA_invol» := P2M_GroundTheory_Heights__Heights_StrongApprox_sigA_invol_a7260028bf49
