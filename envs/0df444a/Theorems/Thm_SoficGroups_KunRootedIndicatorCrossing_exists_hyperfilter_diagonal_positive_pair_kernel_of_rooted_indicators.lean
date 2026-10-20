-- Prove2me | Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_exists_hyperfilter_diagonal_positive_pair_kernel_of_rooted_indicators
-- name    : SoficGroups.KunRootedIndicatorCrossing.exists_hyperfilter_diagonal_positive_pair_kernel_of_rooted_indicators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/cafe7267-4952-44e9-a796-09b3224aa3ad
-- title:
--   SoficGroups.KunRootedIndicatorCrossing.exists_hyperfilter_diagonal_positive_pair_kernel_of_rooted_indicators
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology

theorem SoficGroups.KunRootedIndicatorCrossing.exists_hyperfilter_diagonal_positive_pair_kernel_of_rooted_indicators
    {G ι : Type*} [Group G] [Fintype ι] [Nonempty ι]
    {V : ℕ → Type*} [∀ n, Fintype (V n)]
    (p : ∀ n, ι → Equiv.Perm (V n))
    (f : ∀ n, V n → ℝ)
    (σ : ∀ n, G → Equiv.Perm (V n))
    (w : G → List ι)
    (hf : ∀ n x, f n x = 0 ∨ f n x = 1)
    (hdefect : ∀ n, permutationMarkov (p n) (indicatorVector (f n)) ≠
      indicatorVector (f n))
    (hw : ∀ n g, σ n g = ((w g).map (p n)).prod)
    (hroot : ∀ a g : G, ∀ᶠ n in Filter.atTop,
      ∀ x : V n, indicatorVector (f n) x ≠ 0 →
        σ n (a * g) x = (σ n a * σ n g) x) :
    ∃ K : Matrix (G × G) (G × G) ℂ,
      K.PosSemidef ∧
      (∀ a g h j k : G,
        K (a * g, a * h) (a * j, a * k) = K (g, h) (j, k)) ∧
      (∀ g h j : G, ∀ q : G × G,
        K (g, h) q + K (h, j) q = K (g, j) q) ∧
      ∀ q r,
        Tendsto
          (fun n =>
            ⟪normalizedPairDisplacement (p n) (f n) (σ n) q,
              normalizedPairDisplacement (p n) (f n) (σ n) r⟫_ℂ)
          (Filter.hyperfilter ℕ) (𝓝 (K q r)) := by sorry
