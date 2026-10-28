-- Prove2me | Theorems.Thm_Submodule_starProjection_map_eq_zero_iff_forall_dotProduct
-- name    : Submodule.starProjection_map_eq_zero_iff_forall_dotProduct
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T05:14:59.908621+00:00
-- url     : https://prove2.me/theorems/52f3f01b-886c-4ff6-a22b-e97f0322e58f
-- title:
--   The orthogonal projection onto a subspace vanishes exactly on its annihilator
-- statement:
--   Let $V \subseteq \mathbb{R}^{N}$ be a linear subspace and let $b \in \mathbb{R}^{N}$. Carry $V$
--   over to the Euclidean space $\ell^2(N)$ and let $P_V$ be the orthogonal projection onto its
--   image. Then the projection of $b$ vanishes exactly when $b$ is orthogonal to $V$:
--
--   $$
--   P_V b = 0 \iff b \cdot v = 0 \ \text{ for every } v \in V .
--   $$
--
--   This is the bridge between the two ways a vector can be said to be orthogonal to a subspace --
--   the projection being zero, and every pairing vanishing -- and it is needed whenever a problem
--   stated with plain dot products has to be handed to the Hilbert-space machinery, where
--   projections live. It is stated here for the coordinate space so that no transfer of the
--   statement is needed at the point of use.
-- source:
--   S. Zymler, D. Kuhn and B. Rustem, Distributionally robust joint chance constraints with second-order moment information, Mathematical Programming 137 (2013), 167-198. Carved from https://prove2.me/submissions/3c55ced4-4944-4de2-ba43-8110d2682db1, lines 2628-2648 (the goal proof of DRJointCC.Joint.theorem_3_6, which re-derives it inline; the same block appears in https://prove2.me/submissions/351d29f4-df20-4118-a8bc-25a1b62a5233 for DRJointCC.Individual.theorem_2_2)

import Mathlib

open Matrix

theorem Submodule.starProjection_map_eq_zero_iff_forall_dotProduct {N : ℕ} (V : Submodule ℝ (Fin N → ℝ))
    (b : Fin N → ℝ) :
    (V.map (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm.toLinearMap).starProjection
        (WithLp.toLp 2 b) = 0 ↔ ∀ v ∈ V, b ⬝ᵥ v = 0 := by sorry
