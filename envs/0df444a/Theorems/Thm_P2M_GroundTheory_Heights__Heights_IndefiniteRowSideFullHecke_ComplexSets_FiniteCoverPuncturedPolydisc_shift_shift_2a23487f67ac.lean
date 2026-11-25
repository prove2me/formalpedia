-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteCoverPuncturedPolydisc_shift_shift_2a23487f67ac
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteCoverPuncturedPolydisc_shift_shift_2a23487f67ac
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:54.291976+00:00
-- url     : https://prove2.me/theorems/14081999-b7fb-4cb5-882e-683c1c6c57c9
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Finite Cover Punctured Polydisc shift shift 2a23487f67ac: P2 M Ground Theory Heights  Heights Indefinite Row Side Full H
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Finite Cover Punctured Polydisc shift shift 2a23487f67ac construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Finite Cover Punctured Polydisc shift shift 2a23487f67ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteCoverPuncturedPolydisc.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteCoverPuncturedPolydisc.lean#L67-L72

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteCoverPuncturedPolydisc_shift_shift_2a23487f67ac (c : Fin (e + 1) → ℂ) (ρ : ℝ) (k l : ℤ) (u : strip c ρ) :
    shift c ρ k (shift c ρ l u) = shift c ρ (k + l) u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«FiniteCoverPuncturedPolydisc».«shift_shift» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteCoverPuncturedPolydisc_shift_shift_2a23487f67ac
