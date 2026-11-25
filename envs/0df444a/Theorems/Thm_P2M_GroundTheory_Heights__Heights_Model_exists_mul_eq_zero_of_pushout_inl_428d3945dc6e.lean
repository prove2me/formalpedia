-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_mul_eq_zero_of_pushout_inl_428d3945dc6e
-- name    : P2M_GroundTheory_Heights__Heights_Model_exists_mul_eq_zero_of_pushout_inl_428d3945dc6e
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:57.182606+00:00
-- url     : https://prove2.me/theorems/0dabf081-97a3-4bbf-9bf2-ccd45930f792
-- title:
--   P2 M Ground Theory Heights  Heights Model exists mul eq zero of pushout inl 428d3945dc6e: P2 M Ground Theory Heights  Heights Model exists mul eq zero of pushout inl 428d3945dc6e
-- statement:
--   The P2 M Ground Theory Heights  Heights Model exists mul eq zero of pushout inl 428d3945dc6e construction uses the P2 M Ground Theory Heights  Heights Model exists mul eq zero of pushout inl 428d3945dc6e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PLocSectionsInj.lean#L47-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PLocSectionsInj.lean#L47-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsLocSectionsInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PLocSectionsInj
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
open CategoryTheory Limits AlgebraicGeometry Opposite
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Model_exists_mul_eq_zero_of_pushout_inl_428d3945dc6e {R A T : CommRingCat.{0}} (f : R ⟶ A) (g : R ⟶ T)
    (M : Submonoid R) (hT : @IsLocalization R _ M T _ g.hom.toAlgebra) (a : A)
    (ha : pushout.inl f g a = 0) : ∃ m ∈ M, f m * a = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«exists_mul_eq_zero_of_pushout_inl» := P2M_GroundTheory_Heights__Heights_Model_exists_mul_eq_zero_of_pushout_inl_428d3945dc6e
