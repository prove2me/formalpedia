-- Prove2me | Theorems.Thm_SoficGroups_KunRootedWordPower_tendsto_norm_pairedDefectWordAverage_of_gram
-- name    : SoficGroups.KunRootedWordPower.tendsto_norm_pairedDefectWordAverage_of_gram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/40e2a671-a3f9-49b1-af63-e28bd8fe0df0
-- title:
--   SoficGroups.KunRootedWordPower.tendsto_norm_pairedDefectWordAverage_of_gram
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u v w

theorem SoficGroups.KunRootedWordPower.tendsto_norm_pairedDefectWordAverage_of_gram
    {G ι N H : Type*} [Group G] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {E : N → Type*}
    [∀ n, NormedAddCommGroup (E n)]
    [∀ n, InnerProductSpace ℂ (E n)]
    (l : Filter N) (s : ι → G)
    (z : ∀ n, G × G → E n) (v : G × G → H)
    (hgram : ∀ q r,
      Tendsto (fun n => ⟪z n q, z n r⟫_ℂ) l
        (𝓝 ⟪v q, v r⟫_ℂ))
    (k : ℕ) :
    Tendsto
      (fun n => ‖pairedDefectWordAverage s (z n) k‖)
      l
      (𝓝 ‖pairedDefectWordAverage s v k‖) := by sorry
