-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicOnSubset_differentiableAt_comp_a8c1a300de3d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicOnSubset_differentiableAt_comp_a8c1a300de3d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:49:05.4026+00:00
-- url     : https://prove2.me/theorems/0613744a-bf29-4fa8-bece-2b1ed408448e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Holomorphic On Subset differentiable At comp a8c1a300de3d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Holomorphic On Subset differentiable At comp a8c1a300de3d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Holomorphic On Subset differentiable At comp a8c1a300de3d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalTrace.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalTrace.lean#L26-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalTrace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalBranchedCovering
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalTrace
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicOnSubset_differentiableAt_comp_a8c1a300de3d {σ : Type*} [Fintype σ] {k : ℕ}
    {g : (σ → ℂ) → ℂ} {S : Set (σ → ℂ)} (hg : HolomorphicOnSubset g S)
    {s : (Fin k → ℂ) → σ → ℂ} {y : Fin k → ℂ} (hs : DifferentiableAt ℂ s y)
    (hS : ∀ᶠ y' in 𝓝 y, s y' ∈ S) : DifferentiableAt ℂ (fun y' => g (s y')) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«HolomorphicOnSubset».«differentiableAt_comp» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicOnSubset_differentiableAt_comp_a8c1a300de3d
