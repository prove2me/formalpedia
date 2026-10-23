-- Prove2me | Theorems.Thm_PermInvConvex_Sparsity_theorem_3_1
-- name    : PermInvConvex.Sparsity.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:51.75579+00:00
-- url     : https://prove2.me/theorems/27b8f70a-3839-4c75-8380-66e98fad5208
-- title:
--   Theorem 3.1, p. 8 — the induced norm in closed form: ‖x‖c = ‖u(x)‖s
-- statement:
--   Let $\|\cdot\|_s$ be a symmetric gauge function on $\mathbb R^n$, $1 < K < n$, and $\|\cdot\|_c$ the gauge of $\operatorname{conv}(N^K_{\|\cdot\|_s})$. For every $x \in \mathbb R^n$, with $u(x)$ the closed-form vector (15),
--   $$\|x\|_c = \|u(x)\|_s.$$
--
--   The norm whose unit ball is the convex hull of the sparse set is thus computable from one sort of $|x|$ and one evaluation of $\|\cdot\|_s$; for the $\ell_2$ norm this recovers the $K$-support norm.
--
--   **Formalization Note** $1 < K < n$ is the standing assumption of §3 (p. 6). $\|\cdot\|_c$ is Mathlib's `gauge` of the convex hull.
-- source:
--   Kim, Tawarmalani, Richard, Convexification of Permutation-Invariant Sets and an Application to Sparse PCA, arXiv:1910.02573v2, p. 8, Theorem 3.1 (standing assumption 1 < K < n, p. 6)

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR
import Definitions.Def_PermInvConvex_Sparsity_Majorization
import Definitions.Def_PermInvConvex_Sparsity_Setting

namespace PermInvConvex.Sparsity

theorem theorem_3_1 {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (K : ℕ) (hK : 1 < K) (hKn : K < n) (x : Fin n → ℝ) :
    normC ns K x = ns (uVec K x) := by sorry

end PermInvConvex.Sparsity
