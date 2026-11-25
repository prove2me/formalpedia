-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsRegularPointOf_exists_ball_chart_9fbbc9253110
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsRegularPointOf_exists_ball_chart_9fbbc9253110
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:20:26.773802+00:00
-- url     : https://prove2.me/theorems/23a93096-938c-42b6-a4b3-1d9e86ec725a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Is Regular Point Of exists ball chart 9fbbc9253110: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke C
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Is Regular Point Of exists ball chart 9fbbc9253110 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Is Regular Point Of exists ball chart 9fbbc9253110 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegularLocusIdentity.lean#L10-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegularLocusIdentity.lean#L10-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularLocusIdentity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularOffHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularLocusIdentity
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
open MvPolynomial Topology Filter

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsRegularPointOf_exists_ball_chart_9fbbc9253110 {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {z : σ → ℂ}
    (hz : IsRegularPointOf Y z) {W : Set (σ → ℂ)} (hW : W ∈ 𝓝 z) :
    ∃ (d : ℕ) (V : Set (σ → ℂ)) (B : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧ IsOpen B ∧ IsPreconnected B ∧ AnalyticOnNhd ℂ g B ∧
        Y ∩ V = g '' B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«IsRegularPointOf».«exists_ball_chart» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsRegularPointOf_exists_ball_chart_9fbbc9253110
