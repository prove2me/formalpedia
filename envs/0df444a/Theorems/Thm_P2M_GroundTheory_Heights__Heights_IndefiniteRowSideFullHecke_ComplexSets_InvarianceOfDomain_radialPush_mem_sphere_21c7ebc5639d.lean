-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InvarianceOfDomain_radialPush_mem_sphere_21c7ebc5639d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InvarianceOfDomain_radialPush_mem_sphere_21c7ebc5639d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:20:22.386606+00:00
-- url     : https://prove2.me/theorems/bb8e4bad-9ba2-4583-8d01-8d7f70f14b45
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Invariance Of Domain radial Push mem sphere 21c7ebc5639d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full H
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Invariance Of Domain radial Push mem sphere 21c7ebc5639d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Invariance Of Domain radial Push mem sphere 21c7ebc5639d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PInvarianceOfDomain.lean#L104-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PInvarianceOfDomain.lean#L104-L110

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InvarianceOfDomain_radialPush_mem_sphere_21c7ebc5639d {c y : Fin n → ℝ} {ρ : ℝ} (hy : dist y c < ρ) (hyc : y ≠ c) :
    radialPush c ρ y ∈ sphere c ρ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«InvarianceOfDomain».«radialPush_mem_sphere» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InvarianceOfDomain_radialPush_mem_sphere_21c7ebc5639d
