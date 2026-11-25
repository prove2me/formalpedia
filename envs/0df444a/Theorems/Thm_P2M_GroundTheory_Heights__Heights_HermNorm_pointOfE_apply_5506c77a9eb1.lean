-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_pointOfE_apply_5506c77a9eb1
-- name    : P2M_GroundTheory_Heights__Heights_HermNorm_pointOfE_apply_5506c77a9eb1
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:19:10.513508+00:00
-- url     : https://prove2.me/theorems/d8753b1f-192a-4c9e-b9ce-3d8f86ee90eb
-- title:
--   P2 M Ground Theory Heights  Heights Herm Norm point Of E apply 5506c77a9eb1: P2 M Ground Theory Heights  Heights Herm Norm point Of E apply 5506c77a9eb1
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Norm point Of E apply 5506c77a9eb1 construction uses the P2 M Ground Theory Heights  Heights Herm Norm point Of E apply 5506c77a9eb1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSmoothLocalGraph.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSmoothLocalGraph.lean#L56-L57

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

theorem P2M_GroundTheory_Heights__Heights_HermNorm_pointOfE_apply_5506c77a9eb1 (h : HermNorm n) (v : EuclideanSpace ℂ (Fin n)) :
    h.pointOfE v = h.pointOf v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermNorm».«pointOfE_apply» := P2M_GroundTheory_Heights__Heights_HermNorm_pointOfE_apply_5506c77a9eb1
