-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalModelFibre_eventually_mem_of_fibre_subset_5bca31cfcf03
-- name    : P2M_GroundTheory_Heights__Heights_NormalModelFibre_eventually_mem_of_fibre_subset_5bca31cfcf03
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:04:33.900863+00:00
-- url     : https://prove2.me/theorems/fd91afed-fa93-5d46-8d9b-c0275ca89259
-- title:
--   P2 M Ground Theory Heights  Heights Normal Model Fibre eventually mem of fibre subset 5bca31cfcf03: P2 M Ground Theory Heights  Heights Normal Model Fibre eventually mem of fibre subset 5bca31cfcf03
-- statement:
--   The P2 M Ground Theory Heights  Heights Normal Model Fibre eventually mem of fibre subset 5bca31cfcf03 construction uses the P2 M Ground Theory Heights  Heights Normal Model Fibre eventually mem of fibre subset 5bca31cfcf03 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/NormalModelFibreNear.lean#L71-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/NormalModelFibreNear.lean#L71-L92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PModelLocalizationMaximalPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_NormalModelFibreNear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology ComplexSets Metric
noncomputable section
open GroundTheory.Heights₂.Heights.NormalModelFibre
variable {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)

theorem P2M_GroundTheory_Heights__Heights_NormalModelFibre_eventually_mem_of_fibre_subset_5bca31cfcf03 {q : Fin n → ℂ} {U : Set (Fin n ⊕ Fin M.m → ℂ)} (hU : IsOpen U)
    (hfib : ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q → w ∈ U) :
    ∃ N ∈ 𝓝 q, ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ N → w ∈ U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalModelFibre».«eventually_mem_of_fibre_subset» := P2M_GroundTheory_Heights__Heights_NormalModelFibre_eventually_mem_of_fibre_subset_5bca31cfcf03
