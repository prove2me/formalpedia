-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germ_prod_eventually_zero_3a8cb7987426
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germ_prod_eventually_zero_3a8cb7987426
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:47.253728+00:00
-- url     : https://prove2.me/theorems/d73b88aa-5584-42eb-954c-fffee22c4854
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets germ prod eventually zero 3a8cb7987426: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets germ prod eventually zero 3a8cb7987426 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets germ prod eventually zero 3a8cb7987426 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteGermProjectionOpenAt.lean#L29-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteGermProjectionOpenAt.lean#L29-L46

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germ_prod_eventually_zero_3a8cb7987426 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*}
    (h : ι → E → ℂ) {y : E} (s : Finset ι) (han : ∀ i ∈ s, AnalyticAt ℂ (h i) y)
    (hprod : ∀ᶠ z in 𝓝 y, ∏ i ∈ s, h i z = 0) : ∃ i ∈ s, ∀ᶠ z in 𝓝 y, h i z = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«germ_prod_eventually_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germ_prod_eventually_zero_3a8cb7987426
