-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PuncturedBranchSameOrder_disc_props_e21f27b8168e
-- name    : P2M_GroundTheory_Heights__Heights_PuncturedBranchSameOrder_disc_props_e21f27b8168e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:04.216806+00:00
-- url     : https://prove2.me/theorems/bdbca4ba-e43d-4380-b288-bfe04f08b4a5
-- title:
--   P2 M Ground Theory Heights  Heights Punctured Branch Same Order disc props e21f27b8168e: P2 M Ground Theory Heights  Heights Punctured Branch Same Order disc props e21f27b8168e
-- statement:
--   The P2 M Ground Theory Heights  Heights Punctured Branch Same Order disc props e21f27b8168e construction uses the P2 M Ground Theory Heights  Heights Punctured Branch Same Order disc props e21f27b8168e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPuncturedBranchSameOrder.lean#L18-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPuncturedBranchSameOrder.lean#L18-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedBranchSameOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedCurveDiscInverse
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPuncturedBranchSameOrder
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
open MvPolynomial ComplexSets Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.PuncturedBranchSameOrder

theorem P2M_GroundTheory_Heights__Heights_PuncturedBranchSameOrder_disc_props_e21f27b8168e {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ} (b : VarBranch I 1 q) :
    DifferentiableOn ℂ (fun τ : ℂ ↦ b.toFun fun _ ↦ τ) (Metric.ball 0 b.radius) ∧
    Set.InjOn (fun τ : ℂ ↦ b.toFun fun _ ↦ τ) (Metric.ball 0 b.radius) ∧
    Set.MapsTo (fun τ : ℂ ↦ b.toFun fun _ ↦ τ) (Metric.ball 0 b.radius) (zeroSet I) ∧
    (b.toFun fun _ ↦ (0 : ℂ)) = q ∧
    ∀ x, x ∈ b.image ↔ ∃ σ ∈ Metric.ball (0 : ℂ) b.radius, (b.toFun fun _ ↦ σ) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PuncturedBranchSameOrder».«disc_props» := P2M_GroundTheory_Heights__Heights_PuncturedBranchSameOrder_disc_props_e21f27b8168e
