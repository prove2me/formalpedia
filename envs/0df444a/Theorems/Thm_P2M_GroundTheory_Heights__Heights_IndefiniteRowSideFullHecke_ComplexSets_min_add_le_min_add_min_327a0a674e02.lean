-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_min_add_le_min_add_min_327a0a674e02
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_min_add_le_min_add_min_327a0a674e02
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:21:40.399832+00:00
-- url     : https://prove2.me/theorems/a995974e-3388-48db-88e8-2044426bf65c
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets min add le min add min 327a0a674e02: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets min
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets min add le min add min 327a0a674e02 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets min add le min add min 327a0a674e02 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSerreSFlatAscent.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSerreSFlatAscent.lean#L17-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreConditions
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreSFlatAscent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatDimFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatLocalRegularSequence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSerreSFlatAscent
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_min_add_le_min_add_min_327a0a674e02 {k a b : WithBot ℕ∞} (hk : 0 ≤ k) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min k (a + b) ≤ min k a + min k b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«min_add_le_min_add_min» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_min_add_le_min_add_min_327a0a674e02
