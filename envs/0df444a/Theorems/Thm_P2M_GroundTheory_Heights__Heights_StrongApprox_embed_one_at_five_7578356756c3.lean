-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_embed_one_at_five_7578356756c3
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_embed_one_at_five_7578356756c3
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:39:04.220692+00:00
-- url     : https://prove2.me/theorems/5f6d8aeb-689a-5326-b101-7b8c000fcc23
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx embed one at five 7578356756c3: P2 M Ground Theory Heights  Heights Strong Approx embed one at five 7578356756c3
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx embed one at five 7578356756c3 construction uses the P2 M Ground Theory Heights  Heights Strong Approx embed one at five 7578356756c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L383-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L383-L384

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_embed_one_at_five_7578356756c3 : embed GaussQ v5 (1 : Matrix (Fin 2) (Fin 2) (Kv GaussQ v5)) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«embed_one_at_five» := P2M_GroundTheory_Heights__Heights_StrongApprox_embed_one_at_five_7578356756c3
