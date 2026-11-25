-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_coneTangent_eq_comap_4e9c06d4baf9
-- name    : P2M_GroundTheory_Heights__Heights_coneTangent_eq_comap_4e9c06d4baf9
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:46:11.601823+00:00
-- url     : https://prove2.me/theorems/cf18070d-2f16-4b56-8270-46ed290d4169
-- title:
--   P2 M Ground Theory Heights  Heights cone Tangent eq comap 4e9c06d4baf9: P2 M Ground Theory Heights  Heights cone Tangent eq comap 4e9c06d4baf9
-- statement:
--   The P2 M Ground Theory Heights  Heights cone Tangent eq comap 4e9c06d4baf9 construction uses the P2 M Ground Theory Heights  Heights cone Tangent eq comap 4e9c06d4baf9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSmoothLocalGraph.lean#L86-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSmoothLocalGraph.lean#L86-L89

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

theorem P2M_GroundTheory_Heights__Heights_coneTangent_eq_comap_4e9c06d4baf9 (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (z : EuclideanSpace ℂ (Fin n)) :
    coneTangent h J z = (polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) (h.pointOf z)).comap
      (h.pointOfE : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«coneTangent_eq_comap» := P2M_GroundTheory_Heights__Heights_coneTangent_eq_comap_4e9c06d4baf9
