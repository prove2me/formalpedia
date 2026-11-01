-- Prove2me | Theorems.Thm_PfisterCEP_allOnes_eigensystem
-- name    : PfisterCEP.allOnes_eigensystem
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:26:03.164629+00:00
-- url     : https://prove2.me/theorems/919aa515-27be-4282-9642-c3d2ab5f3775
-- title:
--   Eigensystem of the all-ones matrix: eigenvalues $\{N,0,\dots,0\}$
-- statement:
--   Let $J$ be the real $N\times N$ matrix with every entry equal to $1$, and $e_1,\dots,e_N$ the standard basis vectors. Then
--
--   1. $J(1,1,\dots,1)^\top=N\,(1,1,\dots,1)^\top$;
--   2. $J(e_k-e_l)=0$ for all $k,l$;
--   3. the characteristic polynomial of $J$ is $\det(XI-J)=X^N-N\,X^{N-1}$.
--
--   So the eigenvalues of $J$, with multiplicity, are $\{N,0,\dots,0\}$, with eigenvector $(1,\dots,1)$ for $N$ and the vectors $(1,-1,0,\dots,0),\dots,(1,0,\dots,0,-1)$ (the "same respective eigenvectors" as for the GHZ adjacency matrix) for $0$. The eigenvalue $N$ on $(1,\dots,1)$ is the squeezing enhancement factor of the phase sum.
--
--   Differences from the source:
--
--   - generalization: the eigenvectors $(1,-1,0,\dots,0),\dots,(1,0,\dots,0,-1)$ → $e_k-e_l$ for all $k,l$; reason: the page's vectors are $e_1-e_l$, special cases
--   - encoding: eigenvalues $\{N,0,\dots,0\}$ → $\operatorname{charpoly}J=X^N-N X^{N-1}$; reason: the characteristic polynomial records the eigenvalue multiset; at $N=0$ truncated subtraction gives $1$, the characteristic polynomial of the empty matrix
-- source:
--   Pfister, Graph states and carrier-envelope phase squeezing, arXiv:quant-ph/0701104v2, Sec. b, p.2, right column

import Mathlib

namespace PfisterCEP

/-- **Eigensystem of the all-ones matrix: eigenvalues `{N, 0, …, 0}`.**
O. Pfister, *Graph states and carrier-envelope phase squeezing*, arXiv:quant-ph/0701104v2, Sec. b, p.2, right column: "The adjacency matrix has all its elements equal to 1 and has
eigenvalues {N, 0, · · · , 0} with the same respective eigenvectors."

With `J` the `N × N` real matrix of ones:
1. `J (1, …, 1) = N (1, …, 1)`;
2. `J (eₖ − eₗ) = 0` for all `k, l` (this contains the vectors `(1, −1, 0, …, 0)`, …,
   `(1, 0, …, 0, −1)` of the GHZ paragraph);
3. the characteristic polynomial of `J` is `X^N − N X^{N−1}`, i.e. the eigenvalue multiset is
   `{N, 0, …, 0}`.

**Formalization Note** At `N = 0` Lean's truncated `N − 1 = 0` makes clause 3 read `1 = X⁰ − 0·X⁰`,
which is the characteristic polynomial `1` of the empty matrix. -/
theorem allOnes_eigensystem (N : ℕ) : Matrix.mulVec (Matrix.of fun _ _ => (1 : ℝ) : Matrix (Fin N) (Fin N) ℝ) (fun _ => 1) = (N : ℝ) • (fun _ => (1 : ℝ)) ∧ (∀ k l : Fin N, Matrix.mulVec (Matrix.of fun _ _ => (1 : ℝ) : Matrix (Fin N) (Fin N) ℝ) (Pi.single k 1 - Pi.single l 1) = 0) ∧ (Matrix.of fun _ _ => (1 : ℝ) : Matrix (Fin N) (Fin N) ℝ).charpoly = Polynomial.X ^ N - Polynomial.C (N : ℝ) * Polynomial.X ^ (N - 1) := by sorry

end PfisterCEP
