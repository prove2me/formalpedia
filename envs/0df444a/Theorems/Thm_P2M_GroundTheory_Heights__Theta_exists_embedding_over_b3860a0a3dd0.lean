-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_exists_embedding_over_b3860a0a3dd0
-- name    : P2M_GroundTheory_Heights__Theta_exists_embedding_over_b3860a0a3dd0
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:53:39.872211+00:00
-- url     : https://prove2.me/theorems/73d3c7d1-27c1-4803-b252-943cf178601e
-- title:
--   P2 M Ground Theory Heights  Theta exists embedding over b3860a0a3dd0: P2 M Ground Theory Heights  Theta exists embedding over b3860a0a3dd0
-- statement:
--   The P2 M Ground Theory Heights  Theta exists embedding over b3860a0a3dd0 construction uses the P2 M Ground Theory Heights  Theta exists embedding over b3860a0a3dd0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/CMDatum.lean#L131-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/CMDatum.lean#L131-L136

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open NumberField GroundTheory.Automorphic
variable (F E : Type*) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {F E}
variable (F E)
variable {F E}
variable (F E)

theorem P2M_GroundTheory_Heights__Theta_exists_embedding_over_b3860a0a3dd0 (v : InfinitePlace F) :
    ∃ φ : E →+* ℂ, InfinitePlace.mk (φ.comp (algebraMap F E)) = v := by sorry

alias «GroundTheory».«Heights₂».«Theta».«exists_embedding_over» := P2M_GroundTheory_Heights__Theta_exists_embedding_over_b3860a0a3dd0
