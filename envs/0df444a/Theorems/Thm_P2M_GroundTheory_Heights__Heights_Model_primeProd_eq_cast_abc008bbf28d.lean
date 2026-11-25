-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_primeProd_eq_cast_abc008bbf28d
-- name    : P2M_GroundTheory_Heights__Heights_Model_primeProd_eq_cast_abc008bbf28d
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:29:35.306798+00:00
-- url     : https://prove2.me/theorems/f2e4d914-a586-4ff9-9b27-cb62641763f2
-- title:
--   P2 M Ground Theory Heights  Heights Model prime Prod eq cast abc008bbf28d: P2 M Ground Theory Heights  Heights Model prime Prod eq cast abc008bbf28d
-- statement:
--   The P2 M Ground Theory Heights  Heights Model prime Prod eq cast abc008bbf28d construction uses the P2 M Ground Theory Heights  Heights Model prime Prod eq cast abc008bbf28d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueBundles.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueBundles.lean#L37-L39

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

theorem P2M_GroundTheory_Heights__Heights_Model_primeProd_eq_cast_abc008bbf28d (S : Finset Nat.Primes) :
    primeProd S = ((∏ q ∈ S, (q : ℕ) : ℕ) : ℤ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«primeProd_eq_cast» := P2M_GroundTheory_Heights__Heights_Model_primeProd_eq_cast_abc008bbf28d
