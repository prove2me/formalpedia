-- Prove2me | Theorems.Thm_SparseApprox_Greedy_greedy_iterations_le
-- name    : SparseApprox.Greedy.greedy_iterations_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:25:52.090853+00:00
-- url     : https://prove2.me/theorems/84d1a54c-0841-473b-92b2-996b9158bc1a
-- title:
--   Theorem 2 — Greedy selects at most $\lceil 18\,\mathrm{Opt}(\varepsilon/2)\|\mathbf A^+\|_2^2\ln(\|b\|_2/\varepsilon)\rceil$ columns (for $A$ with linearly independent columns)
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have linearly independent columns, let $b\in\mathbb R^m$ and $\varepsilon>0$, and assume that some $x\in\mathbb R^n$ satisfies $\|Ax-b\|_2\le\varepsilon/2$. Let $\mathbf A$ be $A$ with each column normalized in the $L_2$ norm, $\mathbf A^+$ its pseudo-inverse and $\|\mathbf A^+\|_2$ its spectral norm, and let
--   $$\operatorname{Opt}(\varepsilon/2)=\min\{\|x\|_0 : \|Ax-b\|_2\le\varepsilon/2\}$$
--   be the fewest number of nonzero entries over all solutions within error $\varepsilon/2$. Then every run of the selection phase of Algorithm Greedy on input $A,b,\varepsilon$ (with any tie-breaking in the greedy choice) performs a number $t$ of iterations, equal to the number of columns selected, that satisfies
--   $$t\le\Big\lceil 18\,\operatorname{Opt}(\varepsilon/2)\,\|\mathbf A^+\|_2^2\,\ln\Big(\frac{\|b\|_2}{\varepsilon}\Big)\Big\rceil .$$
--   Since the solution phase solves a linear system in the selected columns only, the computed solution has at most this many nonzero entries.
--
--   The theorem shows that the greedy heuristic approximates the NP-hard sparse approximation problem within a factor that depends on the conditioning of $\mathbf A$ and logarithmically on $\|b\|_2/\varepsilon$, at the price of doubling the error tolerance in the comparison with the optimum.
--
--   **Formalization Note** The hypothesis that $A$ has linearly independent columns is added; the printed Theorem 2 is false without it. Counterexample: $m=2$, $n=200$, columns $(\cos\theta_j,\sin\theta_j)$ and $(\sin\theta_j,\cos\theta_j)$ for $100$ distinct $\theta_j\in[0.001,0.01]$, $b=\sqrt2(1,1)$, $\varepsilon=1$: then $\operatorname{Opt}(1/2)=2$ and $\|\mathbf A^+\|_2^2\approx0.0101$, so the bound is $\lceil0.252\rceil=1$, yet Greedy selects two columns. The hypothesis forces $n\le m$ and holds for the paper's motivating nonsingular interpolation systems. The existence hypothesis on $x$ is needed because $\operatorname{Opt}$ is an infimum over ℕ, which is $0$ on the empty set. The ceiling is `Nat.ceil`; when $t\ge1$ we have $\|b\|_2>\varepsilon$, the logarithm is positive and `Nat.ceil` agrees with the integer ceiling. The bound is stated for every prefix of a run, so no run can exceed it. The pseudo-inverse is any matrix satisfying the four Penrose equations for $\mathbf A$.
-- source:
--   Natarajan, Sparse Approximate Solutions to Linear Systems, SIAM J. Comput. 24 (1995), p. 229, Theorem 2, Eq. (1) (proof pp. 230–233, concluding at (34))

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

theorem greedy_iterations_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε)
    (hA : LinearIndependent ℝ (colE A))
    (hfeas : ∃ x : EuclideanSpace ℝ (Fin n), ‖Matrix.toEuclideanLin A x - b‖ ≤ ε / 2)
    (P : Matrix (Fin n) (Fin m) ℝ) (hP : IsMoorePenrose (Abar A) P)
    (k : ℕ → Fin n) (t : ℕ) (hrun : IsGreedyRun A b ε k t) :
    t ≤ ⌈18 * (optSparsity A b (ε / 2) : ℝ) * opNorm2 P ^ 2 * Real.log (‖b‖ / ε)⌉₊ := by sorry

end SparseApprox.Greedy
