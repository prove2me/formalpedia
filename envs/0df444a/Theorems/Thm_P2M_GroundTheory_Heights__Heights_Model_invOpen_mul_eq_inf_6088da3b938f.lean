-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_invOpen_mul_eq_inf_6088da3b938f
-- name    : P2M_GroundTheory_Heights__Heights_Model_invOpen_mul_eq_inf_6088da3b938f
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:34.786179+00:00
-- url     : https://prove2.me/theorems/19b2d935-3983-4681-8ace-0bee25567dd5
-- title:
--   P2 M Ground Theory Heights  Heights Model inv Open mul eq inf 6088da3b938f: P2 M Ground Theory Heights  Heights Model inv Open mul eq inf 6088da3b938f
-- statement:
--   The P2 M Ground Theory Heights  Heights Model inv Open mul eq inf 6088da3b938f construction uses the P2 M Ground Theory Heights  Heights Model inv Open mul eq inf 6088da3b938f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueBundles.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueBundles.lean#L19-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueBundles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
variable {X : Scheme.{0}}

theorem P2M_GroundTheory_Heights__Heights_Model_invOpen_mul_eq_inf_6088da3b938f (f : X ⟶ SpecZ) (a b : ℤ) :
    invOpen f (a * b) = invOpen f a ⊓ invOpen f b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«invOpen_mul_eq_inf» := P2M_GroundTheory_Heights__Heights_Model_invOpen_mul_eq_inf_6088da3b938f
