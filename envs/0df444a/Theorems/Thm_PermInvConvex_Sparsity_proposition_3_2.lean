-- Prove2me | Theorems.Thm_PermInvConvex_Sparsity_proposition_3_2
-- name    : PermInvConvex.Sparsity.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:53.084169+00:00
-- url     : https://prove2.me/theorems/647805ec-88fd-4831-9be2-08c911d066ea
-- title:
--   Proposition 3.2, p. 7 — conv(N^K) is the unit ball of the sign- and permutation-invariant norm ‖·‖c
-- statement:
--   Let $\|\cdot\|_s$ be a symmetric gauge function on $\mathbb R^n$ and $1 < K < n$. Let $\|x\|_c = \inf\{t > 0 \mid x/t \in \operatorname{conv}(N^K_{\|\cdot\|_s})\}$ be the gauge (14) of the convex hull. Then $\|\cdot\|_c$ is a sign- and permutation-invariant norm, and
--   $$\operatorname{conv}\big(N^K_{\|\cdot\|_s}\big) = B_c(1) = \{x \in \mathbb R^n \mid \|x\|_c \le 1\}.$$
--
--   The proposition recasts the convex hull as a norm ball in the original space, which is the form in which Theorem 3.1 evaluates it.
--
--   **Formalization Note** Both parts of the statement are formalized: that $\|\cdot\|_c$ is a symmetric gauge function, and the equality of sets. $1 < K < n$ is the standing assumption of §3 (p. 6).
-- source:
--   Kim, Tawarmalani, Richard, Convexification of Permutation-Invariant Sets and an Application to Sparse PCA, arXiv:1910.02573v2, p. 7, Proposition 3.2 with (14) (standing assumption 1 < K < n, p. 6)

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR
import Definitions.Def_PermInvConvex_Sparsity_Majorization
import Definitions.Def_PermInvConvex_Sparsity_Setting

namespace PermInvConvex.Sparsity

theorem proposition_3_2 {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (K : ℕ) (hK : 1 < K) (hKn : K < n) :
    IsSymmetricGauge (normC ns K) ∧
      convexHull ℝ (NK ns K) = {x | normC ns K x ≤ 1} := by sorry

end PermInvConvex.Sparsity
