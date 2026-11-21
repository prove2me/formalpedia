-- Prove2me | Theorems.Thm_SoSLinAlg_WeakRank_membership_of_vanishing_on_orthogonal_rows
-- name    : SoSLinAlg.WeakRank.membership_of_vanishing_on_orthogonal_rows
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T10:39:04.840928+00:00
-- url     : https://prove2.me/theorems/002e60fb-6e45-409f-8a59-1a3d852a9899
-- title:
--   Proof of Proposition 4.2 — a polynomial vanishing on the real solutions of $X_IY_J^\top=0$ lies in the ideal they generate
-- statement:
--   Let $n, r$ be natural numbers and let $I, J \subseteq \{0,\dots,n-1\}$ be sets of row indices with $|I| + |J| \le r$. Let $X, Y$ be $n \times r$ matrices of real indeterminates, and let $F \in \mathbb{R}[X, Y]$ be a polynomial that vanishes at every pair of real $n \times r$ matrices $(X, Y)$ satisfying $(XY^\top)_{ij} = 0$ for all $i \in I$ and $j \in J$ (only these equations are imposed; the other rows of $X$ and $Y$ are unconstrained). Then there are polynomials $g_{ij}$ with $F = \sum_{i \in I,\, j \in J} g_{ij}\,(XY^\top)_{ij}$.
--
--   This is the step in the paper's proof of Proposition 4.2 (p. 14) that rests on the primality of the ideal $\langle (XY^\top)_{ij} : i \in I, j \in J\rangle$ for $|I| + |J| \le r$, which the paper takes from [CW19, Theorem 8.6(3)] applied to the complete bipartite graph $K_{|I|,|J|}$. The paper applies it to a component $F$ involving only the rows $I$ of $X$ and $J$ of $Y$; here $F$ may involve all variables, which follows from that case by collecting coefficients in the remaining variables. There are no degree bounds on the $g_{ij}$; the degree bound of Proposition 4.2 is obtained afterwards by comparing homogeneous components. For $I = \emptyset$ or $J = \emptyset$ the statement says that a polynomial vanishing everywhere is zero.
-- source:
--   The sum-of-squares complexity of linear-algebraic principles, STOC 2027 submission 1181 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1181.pdf), p. 14-15, proof of Proposition 4.2 (the ideal $\langle (XY^\top)_{ij} : i\in I, j\in J\rangle$ is prime, [CW19, Thm 8.6(3)]).

import Mathlib
import Definitions.Def_SoSLinAlg_WeakRank_Z

open SoSLinAlg.WeakRank

theorem SoSLinAlg.WeakRank.membership_of_vanishing_on_orthogonal_rows {n r : ℕ}
    (I J : Finset (Fin n)) (hIJ : I.card + J.card ≤ r) (F : Poly n r)
    (hF : ∀ X Y : Matrix (Fin n) (Fin r) ℝ, (∀ i ∈ I, ∀ j ∈ J, (X * Y.transpose) i j = 0) →
      MvPolynomial.eval (assignment X Y) F = 0) :
    ∃ g : (Fin n × Fin n) → Poly n r, F = ∑ ij ∈ I ×ˢ J, g ij * xy ij.1 ij.2 := by sorry
