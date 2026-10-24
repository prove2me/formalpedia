-- Prove2me | Theorems.Thm_PermInvConvex_Sparsity_proposition_3_1
-- name    : PermInvConvex.Sparsity.proposition_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:11:01.99503+00:00
-- url     : https://prove2.me/theorems/2734ff7b-8b26-4b22-a56c-46edf5be4fff
-- title:
--   Proposition 3.1, p. 7 — conv(N^K) is a convex body
-- statement:
--   Let $\|\cdot\|_s$ be a symmetric gauge function on $\mathbb R^n$ and $K$ an integer with $1 < K < n$. Then the convex hull
--   $$\operatorname{conv}\big(N^K_{\|\cdot\|_s}\big), \qquad N^K_{\|\cdot\|_s} = \{x \mid \|x\|_s \le 1,\ \operatorname{card}(x) \le K\},$$
--   is a convex body: it is compact, convex, and has nonempty interior.
--
--   This is what allows the paper to define the norm $\|\cdot\|_c$ as the gauge of the hull.
--
--   **Formalization Note** $1 < K < n$ is the standing assumption of §3 (p. 6). Vectors are `Fin n → ℝ` with its product topology.
-- source:
--   Kim, Tawarmalani, Richard, Convexification of Permutation-Invariant Sets and an Application to Sparse PCA, arXiv:1910.02573v2, p. 7, Proposition 3.1 (standing assumption 1 < K < n, p. 6)

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR
import Definitions.Def_PermInvConvex_Sparsity_Majorization
import Definitions.Def_PermInvConvex_Sparsity_Setting

namespace PermInvConvex.Sparsity

theorem proposition_3_1 {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (K : ℕ) (hK : 1 < K) (hKn : K < n) :
    IsConvexBody (convexHull ℝ (NK ns K)) := by sorry

end PermInvConvex.Sparsity
