-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_centred_clear_b016ba46592f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_centred_clear_b016ba46592f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:20:58.362717+00:00
-- url     : https://prove2.me/theorems/4e361ecd-d741-443f-ad3a-7f018b5bcbec
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets centred clear b016ba46592f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets centred clea
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets centred clear b016ba46592f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets centred clear b016ba46592f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitivePresentationCover.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitivePresentationCover.lean#L17-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitivePresentationCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSeparateWeierstrassDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PevEqZeroOfPresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitivePresentationCover
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
open Topology Filter Polynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_centred_clear_b016ba46592f {n : ℕ} (b : Fin n → ℂ) (M : ℕ) (e x : ℂ) :
    (e ^ M * x) ^ n + ∑ j, b j * e ^ (M * (n - j)) * (e ^ M * x) ^ (j : ℕ) =
      e ^ (M * n) * (x ^ n + ∑ j, b j * x ^ (j : ℕ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«centred_clear» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_centred_clear_b016ba46592f
