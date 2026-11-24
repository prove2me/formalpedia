-- Prove2me | Theorems.Thm_SupConGeometry_supcon_repulsion_index_sum
-- name    : SupConGeometry.supcon_repulsion_index_sum
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T01:12:07.215578+00:00
-- url     : https://prove2.me/theorems/d8135369-4bdc-43b1-93b0-4741a221c435
-- title:
--   Lemma 8: lower bound on the sum of inter-class inner products
-- statement:
--   Let $K\le h+1$, $\rho>0$, and let $z_1,\dots,z_N$ lie on the sphere of radius $\rho$ in $\mathbb R^h$, with labels $Y\in[K]^N$. Then
--
--   $$\sum_{y}\ \sum_{n:\,y_n=y}\ \sum_{m:\,y_m\neq y}\langle z_n,z_m\rangle\ \ge\ -\rho^2\sum_y m_Y(y)^2,$$
--
--   with equality if and only if
--   1. (Q5) $\sum_{n\in[N]}z_n=0$, and
--   2. (Q6) $y_n=y_m$ implies $z_n=z_m$.
--
--   This is the step where the zero-mean and class-collapse conditions of the simplex arise.
--
--   **Formalization Note** The printed inner sum has the subscript $y_n\neq y$, which is a typo for $y_m\neq y$ (the proof's first line uses $y_m\neq y$).
-- source:
--   Graf, Hofer, Niethammer and Kwitt, Dissecting Supervised Contrastive Learning, ICML 2021, arXiv:2102.08817v4, Supplementary S1.3, Lemma 8, eq. (90), p. 23; standing assumptions of Supplementary S1, p. 12

import Mathlib
import Definitions.Def_SupConGeometry_Basic

open Finset

namespace SupConGeometry

theorem supcon_repulsion_index_sum {N K h : ℕ} (hKh : K ≤ h + 1)
    (ρ : ℝ) (hρ : 0 < ρ) (Z : Fin N → Rep h) (hZ : ∀ n, ‖Z n‖ = ρ) (Y : Fin N → Fin K) :
    -(ρ ^ 2) * ∑ y, (labelCount Y y : ℝ) ^ 2 ≤
      ∑ y, ∑ n ∈ univ.filter (fun n => Y n = y), ∑ m ∈ univ.filter (fun m => Y m ≠ y),
        inner ℝ (Z n) (Z m) ∧
    (∑ y, ∑ n ∈ univ.filter (fun n => Y n = y), ∑ m ∈ univ.filter (fun m => Y m ≠ y),
        inner ℝ (Z n) (Z m) = -(ρ ^ 2) * ∑ y, (labelCount Y y : ℝ) ^ 2 ↔
      (∑ n, Z n = 0) ∧ ∀ n m : Fin N, Y n = Y m → Z n = Z m) := by sorry

end SupConGeometry
