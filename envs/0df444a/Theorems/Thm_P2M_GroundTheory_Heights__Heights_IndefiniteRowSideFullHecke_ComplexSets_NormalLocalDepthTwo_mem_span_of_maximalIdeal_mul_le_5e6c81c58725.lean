-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalLocalDepthTwo_mem_span_of_maximalIdeal_mul_le_5e6c81c58725
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalLocalDepthTwo_mem_span_of_maximalIdeal_mul_le_5e6c81c58725
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:20:20.837438+00:00
-- url     : https://prove2.me/theorems/5d04dd09-2934-46ae-af52-27d4934478d9
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Normal Local Depth Two mem span of maximal Ideal mul le 5e6c81c58725: P2 M Ground Theory Heights  Heights Indefinite Row
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Normal Local Depth Two mem span of maximal Ideal mul le 5e6c81c58725 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Normal Local Depth Two mem span of maximal Ideal mul le 5e6c81c58725 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalLocalDepthTwo.lean#L9-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalLocalDepthTwo.lean#L9-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalLocalDepthTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalLocalDepthTwo
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
open IsLocalRing RingTheory.Sequence

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalLocalDepthTwo_mem_span_of_maximalIdeal_mul_le_5e6c81c58725 {B : Type*} [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B] (hm : ¬ (maximalIdeal B).IsPrincipal)
    {x y : B} (hx : x ≠ 0) (hy : ∀ a ∈ maximalIdeal B, ∃ b, a * y = x * b) : ∃ c, y = x * c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«NormalLocalDepthTwo».«mem_span_of_maximalIdeal_mul_le» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalLocalDepthTwo_mem_span_of_maximalIdeal_mul_le_5e6c81c58725
