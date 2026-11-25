-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eventually_eq_zero_of_lines_ad69c29afe5f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eventually_eq_zero_of_lines_ad69c29afe5f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:32:40.70942+00:00
-- url     : https://prove2.me/theorems/bbf8b3c6-b9de-4995-a463-c7b6f5dce8fc
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eventually eq zero of lines ad69c29afe5f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Set
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eventually eq zero of lines ad69c29afe5f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eventually eq zero of lines ad69c29afe5f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermFiniteProjection.lean#L9-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermFiniteProjection.lean#L9-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermFiniteProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermFiniteProjection
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
open Topology Filter

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eventually_eq_zero_of_lines_ad69c29afe5f {d : ℕ} {h : (Fin d → ℂ) → ℂ} {a : Fin d → ℂ}
    (ha : AnalyticAt ℂ h a) (hl : ∀ v : Fin d → ℂ, ∀ᶠ t in 𝓝 (0 : ℂ), h (a + t • v) = 0) :
    ∀ᶠ y in 𝓝 a, h y = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«eventually_eq_zero_of_lines» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eventually_eq_zero_of_lines_ad69c29afe5f
