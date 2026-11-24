-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mul_not_mem_prime_iff_cb34b94c57f7
-- name    : P2M_GroundTheory_Heights__Heights_Model_mul_not_mem_prime_iff_cb34b94c57f7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:47.697804+00:00
-- url     : https://prove2.me/theorems/859ba2e6-b95b-482e-811d-e16552ce9957
-- title:
--   P2 M Ground Theory Heights  Heights Model mul not mem prime iff cb34b94c57f7: P2 M Ground Theory Heights  Heights Model mul not mem prime iff cb34b94c57f7
-- statement:
--   The P2 M Ground Theory Heights  Heights Model mul not mem prime iff cb34b94c57f7 construction uses the P2 M Ground Theory Heights  Heights Model mul not mem prime iff cb34b94c57f7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueBundles.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueBundles.lean#L15-L17

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

theorem P2M_GroundTheory_Heights__Heights_Model_mul_not_mem_prime_iff_cb34b94c57f7 {P : Ideal ℤ} (hP : P.IsPrime) (a b : ℤ) :
    a * b ∉ P ↔ a ∉ P ∧ b ∉ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«mul_not_mem_prime_iff» := P2M_GroundTheory_Heights__Heights_Model_mul_not_mem_prime_iff_cb34b94c57f7
