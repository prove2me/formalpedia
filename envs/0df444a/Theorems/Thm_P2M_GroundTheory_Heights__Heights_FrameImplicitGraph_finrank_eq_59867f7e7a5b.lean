-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_finrank_eq_59867f7e7a5b
-- name    : P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_finrank_eq_59867f7e7a5b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:17:44.964075+00:00
-- url     : https://prove2.me/theorems/46fea5e9-ae5e-5191-a40d-d0a465bc3be0
-- title:
--   P2 M Ground Theory Heights  Heights Frame Implicit Graph finrank eq 59867f7e7a5b: P2 M Ground Theory Heights  Heights Frame Implicit Graph finrank eq 59867f7e7a5b
-- statement:
--   The P2 M Ground Theory Heights  Heights Frame Implicit Graph finrank eq 59867f7e7a5b construction uses the P2 M Ground Theory Heights  Heights Frame Implicit Graph finrank eq 59867f7e7a5b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PFrameImplicitGraph.lean#L86-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PFrameImplicitGraph.lean#L86-L94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameImplicitGraph
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HasStrictFDerivAtEval
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameImplicitGraph
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
noncomputable section
open MvPolynomial
open GroundTheory.Heights₂.Heights.FrameImplicitGraph
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_finrank_eq_59867f7e7a5b (I : Finset (Fin n)) :
    Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Module.finrank ℂ ((I → ℂ) × ({j // j ∉ I} → ℂ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FrameImplicitGraph».«finrank_eq» := P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_finrank_eq_59867f7e7a5b
