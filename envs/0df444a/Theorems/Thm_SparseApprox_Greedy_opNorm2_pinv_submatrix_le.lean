-- Prove2me | Theorems.Thm_SparseApprox_Greedy_opNorm2_pinv_submatrix_le
-- name    : SparseApprox.Greedy.opNorm2_pinv_submatrix_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:24:59.118042+00:00
-- url     : https://prove2.me/theorems/b4db90cb-9b46-48a1-bf27-9368c7aebf42
-- title:
--   Proof of Lemma 2, p. 233 — $\|Z^+\|_2\le\|M^+\|_2$ for a column submatrix $Z$ of $M$ (with the added hypothesis that $M$ has linearly independent columns)
-- statement:
--   Let $M\in\mathbb R^{m\times n}$ have linearly independent columns $a_1,\dots,a_n$, let $M^+$ be its pseudo-inverse, let $S\subseteq\{1,\dots,n\}$ and let $Z$ be the $m\times|S|$ matrix with columns $a_i$, $i\in S$, with pseudo-inverse $Z^+$. Then
--   $$\|Z^+\|_2\le\|M^+\|_2 .$$
--
--   In the paper this is argued through singular values: $\|Z^+\|_2$ and $\|M^+\|_2$ are the reciprocals of the smallest nonzero singular values of $Z$ and $M$, and the smallest nonzero singular value of $Z$ is at least that of $M$ (Golub and Van Loan 1983, p. 286). It is the step that turns (31) into Lemma 2.
--
--   **Formalization Note** The hypothesis that $M$ has linearly independent columns is added. The page applies this step to a linearly independent subset of columns of an arbitrary $M=\mathbf A$, and in that generality it is false: for $M=[e_1,\ e_2,\ (e_1+e_2)/\sqrt2]$ one has $\|M^+\|_2=1$, while the independent columns $e_1$ and $(e_1+e_2)/\sqrt2$ form a $Z$ with $\|Z^+\|_2=1/\sqrt{1-1/\sqrt2}\approx1.85$.
-- source:
--   Natarajan, Sparse Approximate Solutions to Linear Systems, SIAM J. Comput. 24 (1995), p. 233, proof of Lemma 2, last paragraph (citing Golub and Van Loan 1983, p. 286)

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

theorem opNorm2_pinv_submatrix_le {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (hM : LinearIndependent ℝ (colE M))
    (P : Matrix (Fin n) (Fin m) ℝ) (hP : IsMoorePenrose M P)
    (S : Finset (Fin n)) (PS : Matrix ↥S (Fin m) ℝ)
    (hPS : IsMoorePenrose (colsMatrix (fun i : ↥S => colE M i)) PS) :
    opNorm2 PS ≤ opNorm2 P := by sorry

end SparseApprox.Greedy
