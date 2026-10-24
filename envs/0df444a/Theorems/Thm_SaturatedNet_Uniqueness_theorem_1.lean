-- Prove2me | Theorems.Thm_SaturatedNet_Uniqueness_theorem_1
-- name    : SaturatedNet.Uniqueness.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:31.478388+00:00
-- url     : https://prove2.me/theorems/d98af484-0642-4d71-9a22-0fab8ae2833c
-- title:
--   Theorem 1, p. 12 — for a non-expansive network, the surplus/exposed/deficit partition (19) is the same for all equilibria
-- statement:
--   Let $(P, w)$ be a non-expansive network ($P \ge 0$, $w \ge 0$, and either $\rho(P) < 1$ or
--   $\rho(P) = 1$ with every basic class final) and let $c \in \mathbb R^n$ be any exogenous flow. For
--   an equilibrium $x$ partition the nodes into
--
--   $$\mathcal V_+^x = \{i : c_i + \textstyle\sum_k P_{ki}x_k > w_i\},\quad
--   \mathcal V_0^x = \{i : 0 \le c_i + \textstyle\sum_k P_{ki}x_k \le w_i\},\quad
--   \mathcal V_-^x = \{i : c_i + \textstyle\sum_k P_{ki}x_k < 0\}.$$
--
--   Then this partition does not depend on the equilibrium: for any two equilibria $x, y$,
--   $\mathcal V_+^x = \mathcal V_+^y$, $\mathcal V_0^x = \mathcal V_0^y$ and $\mathcal V_-^x = \mathcal V_-^y$.
--
--   This invariance is the key structural fact of the paper: once the partition is known, all equilibria
--   solve one linear system (Corollary 1).
--
--   **Formalization Note.** The paper prints the sums as $\sum_{k \ne i}$; they are read as the full
--   sums $\sum_k$, the argument of the saturation in (1), which is how the proof ((21)–(23)) and
--   Remark 5 use them. Example 1 (p. 8) shows that the hypothesis cannot be weakened to $\rho(P) = 1$
--   alone.
-- source:
--   Massai, Como & Fagnani, Equilibria and Systemic Risk in Saturated Networks, arXiv:1912.04815v2, p. 12, Theorem 1 (partition (19), p. 11)

import Mathlib
import Definitions.Def_SaturatedNet_Uniqueness_Model
open Matrix

namespace SaturatedNet.Uniqueness

theorem theorem_1 {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (w : n → ℝ) (hw : 0 ≤ w) (c : n → ℝ) (hne : IsNonExpansive P) :
    ∀ x ∈ equilibria P w c, ∀ y ∈ equilibria P w c,
      surplus P w c x = surplus P w c y ∧ exposed P w c x = exposed P w c y ∧
        deficit P c x = deficit P c y := by sorry

end SaturatedNet.Uniqueness
