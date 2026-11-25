-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_LatticesAgree_proof_a0c829bdedda
-- name    : P2M_GroundTheory_Heights__Heights_Model_LatticesAgree_proof_a0c829bdedda
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:31:50.562315+00:00
-- url     : https://prove2.me/theorems/bdd75d7f-caa0-47ac-8229-ffc8844b4a4f
-- title:
--   P2 M Ground Theory Heights  Heights Model Lattices Agree proof a0c829bdedda: P2 M Ground Theory Heights  Heights Model Lattices Agree proof a0c829bdedda
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Lattices Agree proof a0c829bdedda construction uses the P2 M Ground Theory Heights  Heights Model Lattices Agree proof a0c829bdedda property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PLatticesAgree.lean#L61-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PLatticesAgree.lean#L61-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmulMemOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PLatticesAgree
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

theorem P2M_GroundTheory_Heights__Heights_Model_LatticesAgree_proof_a0c829bdedda (hHOI : HeightOneIntersection.Statement) : LatticesAgree.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«LatticesAgree».«proof» := P2M_GroundTheory_Heights__Heights_Model_LatticesAgree_proof_a0c829bdedda
