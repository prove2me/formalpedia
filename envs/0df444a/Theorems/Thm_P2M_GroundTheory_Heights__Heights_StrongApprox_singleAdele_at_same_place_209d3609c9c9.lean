-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_singleAdele_at_same_place_209d3609c9c9
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_singleAdele_at_same_place_209d3609c9c9
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:39:08.173635+00:00
-- url     : https://prove2.me/theorems/5e362e18-9588-517b-8ba3-8097e8b11ed9
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx single Adele at same place 209d3609c9c9: P2 M Ground Theory Heights  Heights Strong Approx single Adele at same place 209d3609c9c9
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx single Adele at same place 209d3609c9c9 construction uses the P2 M Ground Theory Heights  Heights Strong Approx single Adele at same place 209d3609c9c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L368-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L368-L370

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
open Classical

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_singleAdele_at_same_place_209d3609c9c9 (x : v5.adicCompletion ℚ) : singleF ℚ v5 x v5 = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«singleAdele_at_same_place» := P2M_GroundTheory_Heights__Heights_StrongApprox_singleAdele_at_same_place_209d3609c9c9
