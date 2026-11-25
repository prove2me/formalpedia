-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InvarianceOfDomain_radialPush_of_le_bcd60f3082f5
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InvarianceOfDomain_radialPush_of_le_bcd60f3082f5
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:20:26.05831+00:00
-- url     : https://prove2.me/theorems/fd16da0b-c19d-40c1-80b9-551904d183c5
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Invariance Of Domain radial Push of le bcd60f3082f5: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Invariance Of Domain radial Push of le bcd60f3082f5 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Invariance Of Domain radial Push of le bcd60f3082f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PInvarianceOfDomain.lean#L97-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PInvarianceOfDomain.lean#L97-L102

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInvarianceOfDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBrouwerFixedPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PInvarianceOfDomain
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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain
open Metric Set MeasureTheory
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InvarianceOfDomain_radialPush_of_le_bcd60f3082f5 {c y : Fin n → ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hy : ρ ≤ dist y c) :
    radialPush c ρ y = y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«InvarianceOfDomain».«radialPush_of_le» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InvarianceOfDomain_radialPush_of_le_bcd60f3082f5
