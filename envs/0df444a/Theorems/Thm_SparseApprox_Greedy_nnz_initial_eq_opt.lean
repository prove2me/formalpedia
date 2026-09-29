-- Prove2me | Theorems.Thm_SparseApprox_Greedy_nnz_initial_eq_opt
-- name    : SparseApprox.Greedy.nnz_initial_eq_opt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:23:12.515019+00:00
-- url     : https://prove2.me/theorems/42aeb563-ca47-4b85-9b09-cd99f7888e8a
-- title:
--   p. 233, $N^{(0)}=\operatorname{Opt}(\varepsilon/2)$ (before (32))
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$ and $\varepsilon\in\mathbb R$, and let $\mathbf A=A^{(0)}$ be $A$ with each column normalized in the $L_2$ norm (zero columns stay zero). If $u^{(0)}$ is a vector with the minimum number $N^{(0)}$ of nonzero entries such that $\|\mathbf A u^{(0)}-b\|_2\le\varepsilon/2$, then
--   $$N^{(0)}=\operatorname{Opt}(\varepsilon/2)=\min\{\|x\|_0 : \|Ax-b\|_2\le\varepsilon/2\}.$$
--
--   The sparsity of the best approximate solution does not change when the columns are normalized. This identity links the quantity $N^{(0)}$ of the proof with the $\operatorname{Opt}(\varepsilon/2)$ of Theorem 2.
--
--   **Formalization Note** $\operatorname{Opt}$ is taken over the original matrix $A$, as Theorem 2 prints it; the hypothesis that $u^{(0)}$ exists guarantees that the set defining $\operatorname{Opt}(\varepsilon/2)$ is nonempty.
-- source:
--   Natarajan, Sparse Approximate Solutions to Linear Systems, SIAM J. Comput. 24 (1995), p. 233, first line after the proof of Lemma 3 (before Eq. (32))

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

theorem nnz_initial_eq_opt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (u : EuclideanSpace ℝ (Fin n))
    (hu : IsMinSparseSol (initState A b).col b (ε / 2) u) :
    nnz u = optSparsity A b (ε / 2) := by sorry

end SparseApprox.Greedy
