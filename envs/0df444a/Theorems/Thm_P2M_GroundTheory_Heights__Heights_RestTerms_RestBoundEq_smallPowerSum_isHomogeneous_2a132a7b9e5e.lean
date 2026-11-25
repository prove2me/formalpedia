-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_smallPowerSum_isHomogeneous_2a132a7b9e5e
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_smallPowerSum_isHomogeneous_2a132a7b9e5e
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:20:56.383819+00:00
-- url     : https://prove2.me/theorems/dce4e5e7-c6cb-4870-99e9-d4830fb75497
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq small Power Sum is Homogeneous 2a132a7b9e5e: P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq small Power Sum is Homogeneous 2a
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq small Power Sum is Homogeneous 2a132a7b9e5e construction uses the P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq small Power Sum is Homogeneous 2a132a7b9e5e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/DegPolynomialIsHomogeneous.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/DegPolynomialIsHomogeneous.lean#L60-L65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PRestPolynomialHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PVandermondeOfHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_DegPolynomialIsHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.RestBoundEq

theorem P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_smallPowerSum_isHomogeneous_2a132a7b9e5e (f r a : ℕ) (c : SmallBlock) (m : ℕ) (τ : Fin f) :
    (smallPowerSum f r a c m τ).IsHomogeneous m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«RestBoundEq».«smallPowerSum_isHomogeneous» := P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_smallPowerSum_isHomogeneous_2a132a7b9e5e
