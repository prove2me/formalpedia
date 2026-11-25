-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_sameRationalSpan_onePoint_8fecdd4169a2
-- name    : P2M_GroundTheory_Heights__Heights_Model_sameRationalSpan_onePoint_8fecdd4169a2
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:49:05.841311+00:00
-- url     : https://prove2.me/theorems/73821197-b37f-4384-b04f-480b7b5057c6
-- title:
--   P2 M Ground Theory Heights  Heights Model same Rational Span one Point 8fecdd4169a2: P2 M Ground Theory Heights  Heights Model same Rational Span one Point 8fecdd4169a2
-- statement:
--   The P2 M Ground Theory Heights  Heights Model same Rational Span one Point 8fecdd4169a2 construction uses the P2 M Ground Theory Heights  Heights Model same Rational Span one Point 8fecdd4169a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L676-L696
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L676-L696

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
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
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Model_sameRationalSpan_onePoint_8fecdd4169a2 (o o' : Type) [CommRing o] [CommRing o'] [Algebra o ℚ] [Algebra o' ℚ]
    (h : ∀ a : o, ∃ N : ℕ, 0 < N ∧ ∃ z : ℤ, (N : ℚ) * algebraMap o ℚ a = z)
    (h' : ∀ a : o', ∃ N : ℕ, 0 < N ∧ ∃ z : ℤ, (N : ℚ) * algebraMap o' ℚ a = z) :
    SameRationalSpan ((scaledTrivBundle o onePoint 1 (one_ne_zero (α := ℚ))).lat ())
      ((scaledTrivBundle o' onePoint 1 (one_ne_zero (α := ℚ))).lat ()) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«sameRationalSpan_onePoint» := P2M_GroundTheory_Heights__Heights_Model_sameRationalSpan_onePoint_8fecdd4169a2
