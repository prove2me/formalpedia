-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_ball_diff_countable_8821c6595739
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_ball_diff_countable_8821c6595739
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:20:02.495705+00:00
-- url     : https://prove2.me/theorems/6a0df623-7f82-4a6b-89da-02f7ded33ce1
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Manifold Zeros Complement Connected is Preconnected ball diff countable 8821c6595739: P2 M Ground Theory Heights  Height
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Manifold Zeros Complement Connected is Preconnected ball diff countable 8821c6595739 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Manifold Zeros Complement Connected is Preconnected ball diff countable 8821c6595739 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PManifoldZerosComplementConnected.lean#L42-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PManifoldZerosComplementConnected.lean#L42-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StManifoldZerosComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PManifoldZerosComplementConnected
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
open Topology Filter Set

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_ball_diff_countable_8821c6595739 {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (hE : 1 < Module.rank ℝ E) (c : E) {r : ℝ} (hr : 0 < r)
    {s : Set E} (hs : s.Countable) : IsPreconnected (Metric.ball c r \ s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«ManifoldZerosComplementConnected».«isPreconnected_ball_diff_countable» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_ball_diff_countable_8821c6595739
