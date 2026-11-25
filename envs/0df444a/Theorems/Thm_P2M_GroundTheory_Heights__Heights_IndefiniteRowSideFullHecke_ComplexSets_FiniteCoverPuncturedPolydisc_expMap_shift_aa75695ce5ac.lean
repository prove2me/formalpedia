-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteCoverPuncturedPolydisc_expMap_shift_aa75695ce5ac
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteCoverPuncturedPolydisc_expMap_shift_aa75695ce5ac
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:26.062963+00:00
-- url     : https://prove2.me/theorems/4c4be480-27a4-4176-82cc-c163693da17f
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Finite Cover Punctured Polydisc exp Map shift aa75695ce5ac: P2 M Ground Theory Heights  Heights Indefinite Row Side Full
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Finite Cover Punctured Polydisc exp Map shift aa75695ce5ac construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Finite Cover Punctured Polydisc exp Map shift aa75695ce5ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteCoverPuncturedPolydisc.lean#L103-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteCoverPuncturedPolydisc.lean#L103-L107

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteCoverPuncturedPolydisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteCoverPuncturedPolydisc
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
open Filter Topology Complex
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteCoverPuncturedPolydisc
variable {e : ℕ}
variable {c : Fin (e + 1) → ℂ} {r : ℝ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteCoverPuncturedPolydisc_expMap_shift_aa75695ce5ac (hc : c 0 = 0) {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (k : ℤ) (u : strip c ρ) :
    expMap hc hρ hρr (shift c ρ k u) = expMap hc hρ hρr u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«FiniteCoverPuncturedPolydisc».«expMap_shift» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteCoverPuncturedPolydisc_expMap_shift_aa75695ce5ac
