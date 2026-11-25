-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodPointBranch_exists_branch_4c088d9197c1
-- name    : P2M_GroundTheory_Heights__Heights_GoodPointBranch_exists_branch_4c088d9197c1
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:19:23.46735+00:00
-- url     : https://prove2.me/theorems/36e91b50-23cb-45b5-a498-9369419f416f
-- title:
--   P2 M Ground Theory Heights  Heights Good Point Branch exists branch 4c088d9197c1: P2 M Ground Theory Heights  Heights Good Point Branch exists branch 4c088d9197c1
-- statement:
--   The P2 M Ground Theory Heights  Heights Good Point Branch exists branch 4c088d9197c1 construction uses the P2 M Ground Theory Heights  Heights Good Point Branch exists branch 4c088d9197c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointBranchExists.lean#L13-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointBranchExists.lean#L13-L136

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GoodPointBranchSlice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GoodPointBranchExists
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
open MvPolynomial Filter Topology Matrix ComplexSets Metric Set
noncomputable section
open GroundTheory.Heights₂.Heights.GoodPointBranch

theorem P2M_GroundTheory_Heights__Heights_GoodPointBranch_exists_branch_4c088d9197c1 {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    {u q : Fin n → ℂ} (hqu : linEval u q = 0)
    {A : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)} {O : Set (Fin d → ℂ)} {V : Set (Fin n → ℂ)}
    {g : (Fin d → ℂ) → Fin n → ℂ} (hV : IsOpen V) (hqV : q ∈ V) (hg : AnalyticOnNhd ℂ g O)
    (hAg : ∀ y ∈ O, A (g y) = y) (hS : zeroSet J ∩ {x | linEval u x = 0} ∩ V = g '' O)
    {N₀ : Set (Fin n → ℂ)} (hN₀ : N₀ ∈ 𝓝 q)
    (hdouble : ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, ∀ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal,
      IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' →
        IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ N₀ → w ≠ w' → linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w) = 0)
    {w : Fin n ⊕ Fin M.m → ℂ} (hwq : IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q)
    {r : ℝ} {φ : (Fin (d + 1) → ℂ) → Fin n ⊕ Fin M.m → ℂ} {k : ℕ} (hr : 0 < r)
    (hφd : DifferentiableOn ℂ φ (ball 0 r)) (hφi : InjOn φ (ball 0 r)) (hφ0 : φ 0 = w)
    (hφZ : MapsTo φ (ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal))
    (hφU : ∀ s : ℝ, 0 < s → ∃ U ∈ 𝓝 w, IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U ⊆ φ '' ball 0 s)
    (hvan : VanishesToOrder (fun t => linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t))) r k)
    (hinjD : ∀ v : Fin (d + 1) → ℂ, v 0 = 0 →
      fderiv ℂ (fun t => IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t)) 0 v = 0 → v = 0)
    {G : Set (Fin n ⊕ Fin M.m → ℂ)} (hG : G ∈ 𝓝 w) :
    ∃ γ : VarBranch J (d + 1) q,
      (∃ U ∈ 𝓝 w, ∀ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U,
        IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' ∈ γ.image) ∧
      (∀ x ∈ γ.image, x ∈ N₀ ∧
        ∃ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ G, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' = x) ∧
      (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → x ∈ γ.slice) ∧
      VanishesToOrder (fun t => linEval u (γ.toFun t)) γ.radius k ∧
      Function.Bijective (fderiv ℂ (fun τ => vecCons (τ 0)
        (LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) *ᵥ γ.toFun τ)) (0 : Fin (d + 1) → ℂ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GoodPointBranch».«exists_branch» := P2M_GroundTheory_Heights__Heights_GoodPointBranch_exists_branch_4c088d9197c1
