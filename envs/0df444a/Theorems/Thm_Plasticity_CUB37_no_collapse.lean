-- Prove2me | Theorems.Thm_Plasticity_CUB37_no_collapse
-- name    : Plasticity.CUB37.no_collapse
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T09:01:25.588256+00:00
-- url     : https://prove2.me/theorems/6ffac740-ac2d-438b-8514-c8344bc47b41
-- title:
--   No collapse at matched points
-- statement:
--   Let $X$ and $X'$ be spaces between $c_{00}(\Gamma)$ and $c_0(\Gamma)$, and let $H\colon B_X\to B_{X'}$ be a nonexpansive bijection that moves every coordinate inward: for every $x\in B_X$ and $n\in\Gamma$, $H(x)_n$ lies between $0$ and $x_n$.
--   Call $x$ **matched** in $X'$ if some $w\in X'$ has $w_ix_i>0$ for every $i$ with $x_i\ne0$.
--   If $x\in B_X$ is matched and $x_n\ne0$, then $H(x)_n\neq0$.
--
--   This is the step that excludes the collapse of a coordinate; with it, finitely supported points keep their supports, and the finite cubes become invariant.
--
--   **Formalization Note** The normal form of this card is the one produced by `Plasticity.CUB37.normal_form` after composing with the inverse signed bijection.
-- source:
--   This repository: expositions/c0_between_spaces.md §3, Proposition 2 (three points, base point and collision; invariance of domain on a finite cube)

import Definitions.Def_Plasticity_SeqSpace
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.CUB37
theorem no_collapse {Γ : Type*} (X X' : Submodule ℝ (Linf Γ))
    (hX0 : c00 Γ ≤ X) (hX1 : X ≤ c0 Γ) (hX'0 : c00 Γ ≤ X') (hX'1 : X' ≤ c0 Γ)
    (H : Linf Γ → Linf Γ)
    (hbij : Set.BijOn H (ballIn X) (ballIn X'))
    (hlip : LipschitzOnWith 1 H (ballIn X))
    (hN1 : ∀ x ∈ ballIn X, ∀ n, (0 ≤ x n → 0 ≤ H x n ∧ H x n ≤ x n) ∧
      (x n ≤ 0 → x n ≤ H x n ∧ H x n ≤ 0))
    (x : Linf Γ) (hx : x ∈ ballIn X)
    (hmatch : ∃ w ∈ X', ∀ i, x i ≠ 0 → 0 < w i * x i)
    (n : Γ) (hn : x n ≠ 0) :
    H x n ≠ 0 := by sorry
end Plasticity.CUB37
