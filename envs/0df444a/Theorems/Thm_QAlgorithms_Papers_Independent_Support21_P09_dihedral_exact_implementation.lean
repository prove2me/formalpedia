-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P09_dihedral_exact_implementation
-- name    : QAlgorithms.Papers.Independent.Support21.P09.dihedral_exact_implementation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:48:26.030266+00:00
-- url     : https://prove2.me/theorems/4d0ee4c3-49c6-4d77-ae14-dac9e5f8beed
-- title:
--   Exact efficient dihedral implementation
-- statement:
--   There is a polynomial $p\in\mathbb N[x]$ such that for every $k\ge2$, $m=2^k$, and $a,b\in\mathbb C$ with $|a|^2+|b|^2=1/m$, the $2m$ columns $(a,b\omega^j)^T$ and $(b,a\omega^j)^T$, $0\le j<m$, define a labeled rank-one POVM; here $\omega=e^{2\pi i/m}$. Set
--
--   $$
--   A=\sqrt m\begin{pmatrix}a&b\\overline b&-\overline a\end{pmatrix},\qquad D=(I_2\otimes F_m)Q_k(A^\dagger\otimes I_m),
--   $$
--
--   where $Q_k$ fixes $|x,0\rangle$ and sends $|x,1\rangle$ to $|\overline x,1\rangle$ for $k$-bit strings $x$. Then $D$ is unitary and the first two rows of $D^\dagger$ are exactly the defining matrix $M$. For every qubit density matrix $\rho$, $D$ followed by computational measurement on $\rho\oplus0_{2m-2}$ reproduces $\operatorname{tr}(\rho M_{:,j}M_{:,j}^\dagger)$ at every label. An exact circuit for $D$ on $k+1$ qubits uses at most $p(k)$ arbitrary elementary one- and two-qubit unitary gates, uniformly in $a,b$.
--
--   The tensor identities have dimension $m$: this corrects the printed $I_{m/2}$ in the completion and $I_4$ in the final formula. The input system occupies the final qubit and the other $k$ qubits start at zero.
-- source:
--   Implementation of group-covariant POVMs by orthogonal measurements, arXiv:quant-ph/0407054v1, PDF p. 16, §6.2: dihedral circuit, with dimension typos corrected

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P09

open scoped BigOperators ComplexConjugate

open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

/-- PDF pp.15–17, §6.2: exact dihedral implementation with a uniform polynomial gate bound.
Correct p.16's Ctilde=A tensor I_(m/2) to A tensor I_m, its final I_4 to I_m, and Q_m to
Q_k. These repairs follow from dimensions and Figure 1; Q complements the first k bits
conditioned on the last bit, including its printed overbar. -/
theorem dihedral_exact_implementation :
    ∃ p : Polynomial ℕ, ∀ k : ℕ, 2 ≤ k → ∀ a b : ℂ,
      ‖a‖ ^ 2 + ‖b‖ ^ 2 = (1 : ℝ) / ((2 ^ k : ℕ) : ℝ) →
      let m := 2 ^ k
      let M := dihedralColumns m a b
      let D := dihedralD m a b
      RankOnePOVM M ∧
      (∀ r j, D.conjTranspose (dihedralInclusion k r) j = M r j) ∧
      ImplementsPOVM M D (dihedralInclusion k) ∧
      ∃ circ : Circuit elementaryGates (1 + k), circ.size ≤ p.eval k ∧
        circ.unitary = D.submatrix (registerIndex 1 k) (registerIndex 1 k) := by sorry

end QAlgorithms.Papers.Independent.Support21.P09

end
