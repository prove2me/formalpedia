-- Prove2me | Theorems.Thm_PermInvConvex_Sparsity_proposition_3_3
-- name    : PermInvConvex.Sparsity.proposition_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:47.87128+00:00
-- url     : https://prove2.me/theorems/a4dd956b-7d47-4f85-8896-5045572d7670
-- title:
--   Proposition 3.3, p. 7 — on K-sparse vectors the induced norm ‖·‖c equals ‖·‖s
-- statement:
--   Let $\|\cdot\|_s$ be a symmetric gauge function on $\mathbb R^n$, $1 < K < n$, and $\|\cdot\|_c$ the gauge of $\operatorname{conv}(N^K_{\|\cdot\|_s})$. If $x \in \mathbb R^n$ has $\operatorname{card}(x) \le K$, then
--   $$\|x\|_c = \|x\|_s.$$
--
--   The two norms therefore agree on the sparse vectors, which is how the paper evaluates $\|u(x)\|_c$ for the $K$-sparse vector $u(x)$.
--
--   **Formalization Note** $1 < K < n$ is the standing assumption of §3 (p. 6).
-- source:
--   Kim, Tawarmalani, Richard, Convexification of Permutation-Invariant Sets and an Application to Sparse PCA, arXiv:1910.02573v2, p. 7, Proposition 3.3 (standing assumption 1 < K < n, p. 6)

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR
import Definitions.Def_PermInvConvex_Sparsity_Majorization
import Definitions.Def_PermInvConvex_Sparsity_Setting

namespace PermInvConvex.Sparsity

theorem proposition_3_3 {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (K : ℕ) (hK : 1 < K) (hKn : K < n) (x : Fin n → ℝ) (hx : card x ≤ K) :
    normC ns K x = ns x := by sorry

end PermInvConvex.Sparsity
