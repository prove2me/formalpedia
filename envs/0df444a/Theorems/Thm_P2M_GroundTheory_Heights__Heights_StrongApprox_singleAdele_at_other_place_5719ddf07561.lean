-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_singleAdele_at_other_place_5719ddf07561
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_singleAdele_at_other_place_5719ddf07561
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:39:51.969324+00:00
-- url     : https://prove2.me/theorems/2b27ca2b-8bac-427e-8b9a-3ab6ed2eb654
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx single Adele at other place 5719ddf07561: P2 M Ground Theory Heights  Heights Strong Approx single Adele at other place 5719ddf07561
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx single Adele at other place 5719ddf07561 construction uses the P2 M Ground Theory Heights  Heights Strong Approx single Adele at other place 5719ddf07561 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L373-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L373-L375

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_singleAdele_at_other_place_5719ddf07561 (x : v5.adicCompletion ℚ) : singleF ℚ v5 x v3 = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«singleAdele_at_other_place» := P2M_GroundTheory_Heights__Heights_StrongApprox_singleAdele_at_other_place_5719ddf07561
