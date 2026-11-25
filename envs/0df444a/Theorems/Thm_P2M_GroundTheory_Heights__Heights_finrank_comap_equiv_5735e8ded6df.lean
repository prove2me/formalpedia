-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_finrank_comap_equiv_5735e8ded6df
-- name    : P2M_GroundTheory_Heights__Heights_finrank_comap_equiv_5735e8ded6df
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:46:23.697542+00:00
-- url     : https://prove2.me/theorems/58989ec2-e31c-4a77-adeb-ad188eece78c
-- title:
--   P2 M Ground Theory Heights  Heights finrank comap equiv 5735e8ded6df: P2 M Ground Theory Heights  Heights finrank comap equiv 5735e8ded6df
-- statement:
--   The P2 M Ground Theory Heights  Heights finrank comap equiv 5735e8ded6df construction uses the P2 M Ground Theory Heights  Heights finrank comap equiv 5735e8ded6df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSmoothLocalGraph.lean#L91-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSmoothLocalGraph.lean#L91-L94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSmoothLocalGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsHolomorphicImplicitGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSmoothLocalGraph
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
open MvPolynomial Module
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_finrank_comap_equiv_5735e8ded6df {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (φ : E ≃ₗ[ℂ] F) (S : Submodule ℂ F) :
    finrank ℂ (S.comap (φ : E →ₗ[ℂ] F)) = finrank ℂ S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«finrank_comap_equiv» := P2M_GroundTheory_Heights__Heights_finrank_comap_equiv_5735e8ded6df
