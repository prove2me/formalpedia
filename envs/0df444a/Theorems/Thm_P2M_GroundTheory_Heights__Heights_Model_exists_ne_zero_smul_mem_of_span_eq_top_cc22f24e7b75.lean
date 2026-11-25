-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_ne_zero_smul_mem_of_span_eq_top_cc22f24e7b75
-- name    : P2M_GroundTheory_Heights__Heights_Model_exists_ne_zero_smul_mem_of_span_eq_top_cc22f24e7b75
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:30:29.528396+00:00
-- url     : https://prove2.me/theorems/13c4cf5d-14ef-4931-9733-954bc7571078
-- title:
--   P2 M Ground Theory Heights  Heights Model exists ne zero smul mem of span eq top cc22f24e7b75: P2 M Ground Theory Heights  Heights Model exists ne zero smul mem of span eq top cc22f24e7b75
-- statement:
--   The P2 M Ground Theory Heights  Heights Model exists ne zero smul mem of span eq top cc22f24e7b75 construction uses the P2 M Ground Theory Heights  Heights Model exists ne zero smul mem of span eq top cc22f24e7b75 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PLatticesAgree.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PLatticesAgree.lean#L12-L14

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmulMemOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PLatticesAgree
import Theorems.Thm_UpperTheory_Reformulated_B_SmulMemOfSpanEqTop_exists_ne_zero_smul_mem_of_span_eq_top

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
variable {A : Type} [CommRing A] [IsDomain A]
  {K : Type} [Field K] [Algebra A K] [IsFractionRing A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]

theorem P2M_GroundTheory_Heights__Heights_Model_exists_ne_zero_smul_mem_of_span_eq_top_cc22f24e7b75 (M : Submodule A V)
    (hM : Submodule.span K (M : Set V) = ⊤) (v : V) : ∃ d : A, d ≠ 0 ∧ d • v ∈ M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«exists_ne_zero_smul_mem_of_span_eq_top» := P2M_GroundTheory_Heights__Heights_Model_exists_ne_zero_smul_mem_of_span_eq_top_cc22f24e7b75
