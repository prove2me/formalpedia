-- Prove2me | Theorems.Thm_QAlgorithms_Childs_unmarked_specNorm_le
-- name    : QAlgorithms.Childs.unmarked_specNorm_le
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:36:22.998846+00:00
-- url     : https://prove2.me/theorems/16d31cc2-e883-4561-b06b-21b0ab2b0a2d
-- title:
--   Spectral gap and marked fraction bound the norm of the unmarked block
-- statement:
--   Let $N \ge 2$ and let $P$ be a symmetric $N \times N$ stochastic matrix ($P_{kj} \ge 0$, $\sum_k P_{kj} = 1$ for all $j$, $P = P^{\mathsf T}$) describing a random walk on the vertex set $V = \{1,\dots,N\}$. Let $M \subseteq V$ be a set of marked vertices and let $P_M$ be the matrix obtained from $P$ by deleting the rows and columns indexed by $M$. Let $\delta > 0$ and $\epsilon > 0$.
--
--   **Lemma.** If the second largest eigenvalue of $P$ in absolute value is at most $1-\delta$ (that is, listing the eigenvalues of $P$ with multiplicity, at most one has absolute value greater than $1-\delta$) and $|M| \ge \epsilon N$, then
--   $$
--   \|P_M\| \le 1 - \delta\epsilon,
--   $$
--   where $\|\cdot\|$ is the spectral (operator) norm.
--
--   Together with $\Pr[\text{no marked vertex after } t \text{ steps}] \le \|P_M\|^t$, this gives the classical hitting time $O(1/(\delta\epsilon))$, and it is the input to the quantum walk search bound $O(1/\sqrt{\delta\epsilon})$.
--
--   **Formalization Note** $N \ge 2$ because the source speaks of a second eigenvalue, and $\delta, \epsilon > 0$ because they are a spectral gap and a fraction; without these the statement fails (e.g. $N = 1$, $P = (1)$, $M = V$, $\delta = 3$, $\epsilon = 1$). Symmetry is stated as Hermitian, which for a real matrix is the same thing; the eigenvalues are the Mathlib eigenvalue list of the Hermitian matrix. If $M = V$, $P_M$ is the empty matrix, of norm $0$.
-- source:
--   Andrew Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, PDF p. 93, Lemma 18.2. https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_Walk
set_option autoImplicit false

namespace QAlgorithms.Childs


/-- **Childs, Lemma 18.2** (PDF p. 93; setting §18.4, p. 92). If the second largest eigenvalue of
`P` (in absolute value) is at most `1 − δ` and `|M| ≥ ϵN`, then `‖P_M‖ ≤ 1 − δϵ`.

Standing assumptions of §18.4 (p. 92): `P` is an `N × N` stochastic matrix (column sums `1`,
nonnegative entries, `IsColumnStochastic`), and "from now on the original walk `P` is symmetric"
(for a real matrix, Hermitian = symmetric); `M ⊆ V = Fin N` is the marked set, and `P_M` is `P`
with the rows and columns of the vertices in `M` deleted (`unmarkedSubmatrix P M`, eq. (18.36)).
`‖·‖` is the spectral norm (`specNorm`).

"The second largest eigenvalue in absolute value is at most `1 − δ`": listing the eigenvalues
of `P` with multiplicity (`hsymm.eigenvalues`), at most one of them has absolute value
`> 1 − δ`. `N ≥ 2` because the source speaks of a second eigenvalue; `δ > 0` and `ϵ > 0`
because they are a spectral gap and a marked fraction (with negative `δ, ϵ` and `M = ∅` the
conclusion `1 ≤ 1 − δϵ` fails). -/
theorem unmarked_specNorm_le {N : ℕ} (hN : 2 ≤ N) (P : Matrix (Fin N) (Fin N) ℝ)
    (hP : IsColumnStochastic P) (hsymm : P.IsHermitian) (M : Finset (Fin N)) (δ ϵ : ℝ)
    (hδ : 0 < δ) (hϵ : 0 < ϵ)
    (hgap : (Finset.univ.filter fun i : Fin N => 1 - δ < |hsymm.eigenvalues i|).card ≤ 1)
    (hM : ϵ * (N : ℝ) ≤ (M.card : ℝ)) :
    specNorm (unmarkedSubmatrix P M) ≤ 1 - δ * ϵ := by
  sorry

end QAlgorithms.Childs
