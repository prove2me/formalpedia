-- Prove2me | Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_exists_equivariant_hilbert_normalized_rooted_pair_realization
-- name    : SoficGroups.KunRootedIndicatorCrossing.exists_equivariant_hilbert_normalized_rooted_pair_realization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/9a15475a-94f5-4580-a0e9-e6a2ce96e6b8
-- title:
--   SoficGroups.KunRootedIndicatorCrossing.exists_equivariant_hilbert_normalized_rooted_pair_realization
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

theorem SoficGroups.KunRootedIndicatorCrossing.exists_equivariant_hilbert_normalized_rooted_pair_realization
    {G ι : Type u} [Group G] [Fintype ι] [Nonempty ι]
    {V : ℕ → Type u} [∀ n, Fintype (V n)]
    (p : ∀ n, ι → Equiv.Perm (V n))
    (f : ∀ n, V n → ℝ)
    (σ : ∀ n, G → Equiv.Perm (V n))
    (s : ι → G) (w : G → List ι)
    (hf : ∀ n x, f n x = 0 ∨ f n x = 1)
    (hdefect : ∀ n, permutationMarkov (p n) (indicatorVector (f n)) ≠
      indicatorVector (f n))
    (hw : ∀ n g, σ n g = ((w g).map (p n)).prod)
    (hone : ∀ n, σ n 1 = 1)
    (hgenerator : ∀ n i, σ n (s i) = p n i)
    (hroot : ∀ a g : G, ∀ᶠ n in Filter.atTop,
      ∀ x : V n, indicatorVector (f n) x ≠ 0 →
        σ n (a * g) x = (σ n a * σ n g) x) :
    ∃ (K : Matrix (G × G) (G × G) ℂ)
      (R : EquivariantHilbertKernelRealization K),
      K.PosSemidef ∧
      (∀ a g h j k : G,
        K (a * g, a * h) (a * j, a * k) = K (g, h) (j, k)) ∧
      (∀ a g h : G,
        R.representation a (R.realization.vector (g, h)) =
          R.realization.vector (a * g, a * h)) ∧
      (∀ g h j : G,
        R.realization.vector (g, h) +
          R.realization.vector (h, j) =
            R.realization.vector (g, j)) ∧
      (∀ a g : G,
        equivariantPairCocycle R (a * g) =
          equivariantPairCocycle R a +
            R.representation a (equivariantPairCocycle R g)) ∧
      ‖(Fintype.card ι : ℂ)⁻¹ •
        ∑ i, equivariantPairCocycle R (s i)‖ = 1 ∧
      ∀ q r,
        Tendsto
          (fun n =>
            ⟪normalizedPairDisplacement (p n) (f n) (σ n) q,
              normalizedPairDisplacement (p n) (f n) (σ n) r⟫_ℂ)
          (Filter.hyperfilter ℕ)
          (𝓝 ⟪R.realization.vector q,
            R.realization.vector r⟫_ℂ) := by sorry
