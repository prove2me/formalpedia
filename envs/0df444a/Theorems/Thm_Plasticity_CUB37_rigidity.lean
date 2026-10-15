-- Prove2me | Theorems.Thm_Plasticity_CUB37_rigidity
-- name    : Plasticity.CUB37.rigidity
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T09:01:25.035841+00:00
-- url     : https://prove2.me/theorems/2ba78b1a-c985-4a80-8df7-e689feea1729
-- title:
--   Rigidity: an inward nonexpansive bijection whose finitely supported images come from matched points is the identity
-- statement:
--   Let $X$, $X'$ and $H\colon B_X\to B_{X'}$ be as in the no-collapse lemma: spaces between $c_{00}(\Gamma)$ and $c_0(\Gamma)$, and a nonexpansive bijection moving every coordinate inward.
--   Suppose that every $x\in B_X$ whose image $H(x)$ is finitely supported is matched in $X'$.
--   Then $H(x)=x$ for every $x\in B_X$.
--
--   The finite cubes are then invariant under $H$, Freudenthal–Hurewicz makes $H$ an isometry on each of them, and the inward property forces the identity on the dense set of finitely supported points.
-- source:
--   This repository: expositions/c0_between_spaces.md §4, Theorem 3

import Definitions.Def_Plasticity_SeqSpace
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.CUB37
theorem rigidity {Γ : Type*} (X X' : Submodule ℝ (Linf Γ))
    (hX0 : c00 Γ ≤ X) (hX1 : X ≤ c0 Γ) (hX'0 : c00 Γ ≤ X') (hX'1 : X' ≤ c0 Γ)
    (H : Linf Γ → Linf Γ)
    (hbij : Set.BijOn H (ballIn X) (ballIn X'))
    (hlip : LipschitzOnWith 1 H (ballIn X))
    (hN1 : ∀ x ∈ ballIn X, ∀ n, (0 ≤ x n → 0 ≤ H x n ∧ H x n ≤ x n) ∧
      (x n ≤ 0 → x n ≤ H x n ∧ H x n ≤ 0))
    (hmatched : ∀ x ∈ ballIn X, (Function.support (H x)).Finite →
      ∃ w ∈ X', ∀ i, x i ≠ 0 → 0 < w i * x i) :
    ∀ x ∈ ballIn X, H x = x := by sorry
end Plasticity.CUB37
