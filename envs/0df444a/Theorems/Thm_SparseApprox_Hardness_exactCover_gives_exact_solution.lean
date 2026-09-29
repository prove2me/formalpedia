-- Prove2me | Theorems.Thm_SparseApprox_Hardness_exactCover_gives_exact_solution
-- name    : SparseApprox.Hardness.exactCover_gives_exact_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:26:53.017412+00:00
-- url     : https://prove2.me/theorems/f95dbcc5-e275-4700-99c1-839805b146f4
-- title:
--   Theorem 1, proof (forward direction) — an exact cover gives x = 1_J with Ax = b and exactly m/3 nonzeros
-- statement:
--   Let $S=\{s_1,\dots,s_m\}$ and let $C=c_1,\dots,c_n$ be a list of 3-element subsets of $S$. Let $A\in\mathbb R^{m\times n}$ be the incidence matrix of $C$ ($A_{ij}=1$ if $s_i\in c_j$, else $0$) and $b=(1,\dots,1)\in\mathbb R^m$. If the sub-collection $\{c_j : j\in J\}$ is an exact cover of $S$, then the indicator vector $x=\mathbf 1_J$ ($x_j=1$ for $j\in J$, $x_j=0$ otherwise) satisfies
--
--   $$Ax=b\qquad\text{and}\qquad 3\,\|x\|_0=m,$$
--
--   that is, $x$ solves the system exactly and has exactly $m/3$ nonzero entries.
--
--   This is the forward direction of the equivalence behind Theorem 1: an exact cover yields a solution of the SAS instance (with any tolerance, in particular $\varepsilon=1/2$) with $m/3$ nonzero entries.
--
--   **Formalization Note** "Exactly $m/3$ nonzero entries" is written $3\,\|x\|_0=m$, avoiding natural-number division; it contains the paper's remark that $m$ must be a multiple of $3$ when an exact cover exists. The number of nonzeros of $\mathbf 1_J$ is $|J|$.
-- source:
--   Natarajan, Sparse Approximate Solutions to Linear Systems, SIAM J. Comput. 24 (1995), p. 228, proof of Theorem 1, second-to-last paragraph ("If the X3C instance has a solution, then consider the vector x …")

import Mathlib
import Definitions.Def_SparseApprox_Hardness_Basic

namespace SparseApprox.Hardness

theorem exactCover_gives_exact_solution {m n : ℕ} (C : Fin n → Finset (Fin m))
    (hC : ∀ j, (C j).card = 3) (J : Finset (Fin n)) (hJ : IsExactCover C J) :
    Matrix.toEuclideanLin (incidence C) (indicatorVec J) = onesVec m ∧
      3 * nnz (indicatorVec J) = m := by sorry

end SparseApprox.Hardness
