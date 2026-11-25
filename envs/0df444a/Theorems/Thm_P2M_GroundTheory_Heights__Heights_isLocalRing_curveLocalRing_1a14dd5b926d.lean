-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isLocalRing_curveLocalRing_1a14dd5b926d
-- name    : P2M_GroundTheory_Heights__Heights_isLocalRing_curveLocalRing_1a14dd5b926d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:06:56.453889+00:00
-- url     : https://prove2.me/theorems/b93a971a-cb42-5d10-8b37-c3d3f564e09c
-- title:
--   P2 M Ground Theory Heights  Heights is Local Ring curve Local Ring 1a14dd5b926d: P2 M Ground Theory Heights  Heights is Local Ring curve Local Ring 1a14dd5b926d
-- statement:
--   The P2 M Ground Theory Heights  Heights is Local Ring curve Local Ring 1a14dd5b926d construction uses the P2 M Ground Theory Heights  Heights is Local Ring curve Local Ring 1a14dd5b926d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/POrdFiniteNonZeroDivisor.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/POrdFiniteNonZeroDivisor.lean#L12-L15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StOrdFiniteNonZeroDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_POrdFiniteNonZeroDivisor
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
open MvPolynomial ComplexSets
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_isLocalRing_curveLocalRing_1a14dd5b926d (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    [Nontrivial (curveLocalRing I q)] : IsLocalRing (curveLocalRing I q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isLocalRing_curveLocalRing» := P2M_GroundTheory_Heights__Heights_isLocalRing_curveLocalRing_1a14dd5b926d
