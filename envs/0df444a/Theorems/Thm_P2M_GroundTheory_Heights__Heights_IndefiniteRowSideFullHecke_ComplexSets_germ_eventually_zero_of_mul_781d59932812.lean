-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germ_eventually_zero_of_mul_781d59932812
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germ_eventually_zero_of_mul_781d59932812
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:21:08.741849+00:00
-- url     : https://prove2.me/theorems/d5ee0e2c-4ad7-46a2-8da4-d6a6ac3b860e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets germ eventually zero of mul 781d59932812: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Set
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets germ eventually zero of mul 781d59932812 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets germ eventually zero of mul 781d59932812 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteGermProjectionOpenAt.lean#L11-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteGermProjectionOpenAt.lean#L11-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionOpenAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleFiniteGermProjectionOpenAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteGermProjectionOpenAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germ_eventually_zero_of_mul_781d59932812 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ} {y : E}
    (hf : AnalyticAt ℂ f y) (hg : AnalyticAt ℂ g y) (hfg : ∀ᶠ z in 𝓝 y, f z * g z = 0) :
    (∀ᶠ z in 𝓝 y, f z = 0) ∨ (∀ᶠ z in 𝓝 y, g z = 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«germ_eventually_zero_of_mul» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germ_eventually_zero_of_mul_781d59932812
