-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_root_branch_eventuallyEq_94398728a4f6
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_root_branch_eventuallyEq_94398728a4f6
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:02.11794+00:00
-- url     : https://prove2.me/theorems/f33ee847-4934-41f0-8a3d-aef9485b6020
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets monic root branch eventually Eq 94398728a4f6: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets monic root branch eventually Eq 94398728a4f6 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets monic root branch eventually Eq 94398728a4f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitiveFormFullBranchConstant.lean#L9-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitiveFormFullBranchConstant.lean#L9-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormFullBranchConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveFormFullBranchConstant
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
open Filter Topology

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_root_branch_eventuallyEq_94398728a4f6 {d N : ℕ} (a : Fin N → (Fin d → ℂ) → ℂ) (s : Fin d → ℂ)
    (u v : (Fin d → ℂ) → ℂ) (ha : ∀ j, ContinuousAt (a j) s) (hu : ContinuousAt u s)
    (hv : ContinuousAt v s) (huv : u s = v s)
    (hsep : (Polynomial.X ^ N + ∑ j, Polynomial.C (a j s) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable)
    (hru : ∀ᶠ t in 𝓝 s, u t ^ N + ∑ j, a j t * u t ^ (j : ℕ) = 0)
    (hrv : ∀ᶠ t in 𝓝 s, v t ^ N + ∑ j, a j t * v t ^ (j : ℕ) = 0) : u =ᶠ[𝓝 s] v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«monic_root_branch_eventuallyEq» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_root_branch_eventuallyEq_94398728a4f6
