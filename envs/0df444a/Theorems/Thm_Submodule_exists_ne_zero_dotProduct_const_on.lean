-- Prove2me | Theorems.Thm_Submodule_exists_ne_zero_dotProduct_const_on
-- name    : Submodule.exists_ne_zero_dotProduct_const_on
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T05:15:01.661236+00:00
-- url     : https://prove2.me/theorems/75aaa2ff-6e52-4e9e-9d85-73c1c1661dc9
-- title:
--   A subspace of large enough dimension carries a nonzero vector constant on a set
-- statement:
--   Let $V \subseteq \mathbb{R}^{N}$ be a linear subspace and let $S \subseteq \mathbb{R}^{N}$ be
--   any set. Write $\operatorname{span}_{\mathrm{aff}}(S)$ for the direction space of the affine
--   hull of $S$, and suppose $V$ has at least one more dimension than that:
--
--   $$
--   \dim \operatorname{span}_{\mathrm{aff}}(S) + 1 \le \dim V .
--   $$
--
--   Then $V$ contains a nonzero vector against which all of $S$ pairs to the same value:
--
--   $$
--   \exists\, v \in V, \ v \ne 0, \ \text{ such that } \ s \cdot v = s' \cdot v \quad
--   \text{for all } s, s' \in S .
--   $$
--
--   This is the counting step behind every rank-reduction and support-reduction argument: a
--   direction that is invisible to the data can be followed without changing any of the constraints
--   it is constant on, and the dimension inequality is exactly what guarantees one exists. The
--   conclusion is stated as equality of pairings rather than membership in an annihilator, which is
--   the form the perturbation argument consumes.
-- source:
--   S. Zymler, D. Kuhn and B. Rustem, Distributionally robust joint chance constraints with second-order moment information, Mathematical Programming 137 (2013), 167-198. Carved from https://prove2.me/submissions/3c55ced4-4944-4de2-ba43-8110d2682db1, lines 2489-2526 (the goal proof of DRJointCC.Joint.theorem_3_6, which re-derives it inline; the same block appears in https://prove2.me/submissions/351d29f4-df20-4118-a8bc-25a1b62a5233 for DRJointCC.Individual.theorem_2_2)

import Mathlib

open Matrix

theorem Submodule.exists_ne_zero_dotProduct_const_on {N : ℕ} (V : Submodule ℝ (Fin N → ℝ))
    (S : Set (Fin N → ℝ))
    (h : Module.finrank ℝ (vectorSpan ℝ S) + 1 ≤ Module.finrank ℝ V) :
    ∃ v ∈ V, v ≠ 0 ∧ ∀ s ∈ S, ∀ s' ∈ S, s ⬝ᵥ v = s' ⬝ᵥ v := by sorry
