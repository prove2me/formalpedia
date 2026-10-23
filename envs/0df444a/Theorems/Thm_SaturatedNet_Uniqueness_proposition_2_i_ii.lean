-- Prove2me | Theorems.Thm_SaturatedNet_Uniqueness_proposition_2_i_ii
-- name    : SaturatedNet.Uniqueness.proposition_2_i_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:30.908919+00:00
-- url     : https://prove2.me/theorems/11866afd-2309-4426-9e52-373b3698f5da
-- title:
--   Proposition 2 (i)–(ii), p. 9 — Perron–Frobenius: ρ(P) has nonnegative right and left eigenvectors, and principal blocks have smaller spectral radius
-- statement:
--   Let $P \in \mathbb R_+^{n \times n}$ be a nonnegative square matrix and let $\rho(P)$ be its
--   spectral radius (the largest modulus of a complex eigenvalue). Then:
--
--   1. (if $n \ge 1$) $\rho(P)$ is an eigenvalue of $P$, and there are vectors
--      $p, \pi \in \mathbb R_+^n \setminus \{0\}$ with
--      $$P p = \rho(P)\, p, \qquad \pi^\top P = \rho(P)\, \pi^\top;$$
--      such vectors are called right and left *dominant eigenvectors* of $P$;
--   2. for every principal square sub-matrix $Q$ of $P$ (rows and columns indexed by the same set $S$),
--      $\rho(Q) \le \rho(P)$.
--
--   These are the classical Perron–Frobenius facts for nonnegative matrices that the uniqueness theory
--   rests on: (ii) gives $\rho(P^{(ll)}) \le \rho(P)$ for every class, and (i) provides the vectors
--   $p$, $\pi$ appearing in Proposition 5 and Theorem 2.
--
--   **Formalization Note.** Item (i) is stated under the hypothesis that the node type is nonempty
--   (there is no nonzero vector on an empty index set; the paper's $n \ge 1$ is implicit). The
--   eigenvalue claim is carried by the nonzero eigenvector $p$. The spectral radius is taken over
--   $\mathbb C$ in $[0,\infty]$ and converted to a real number for the eigen-equations; it is finite.
--   In (ii), $S = \emptyset$ is allowed (its block has spectral radius $0$).
-- source:
--   Massai, Como & Fagnani, Equilibria and Systemic Risk in Saturated Networks, arXiv:1912.04815v2, p. 9, Proposition 2 (i)–(ii)

import Mathlib
import Definitions.Def_SaturatedNet_Uniqueness_Model
open Matrix

namespace SaturatedNet.Uniqueness

theorem proposition_2_i_ii {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) :
    (Nonempty n → ∃ p π : n → ℝ, 0 ≤ p ∧ p ≠ 0 ∧ 0 ≤ π ∧ π ≠ 0 ∧
      P *ᵥ p = (specRad P).toReal • p ∧ π ᵥ* P = (specRad P).toReal • π) ∧
    (∀ S : Finset n, specRad (block P S) ≤ specRad P) := by sorry

end SaturatedNet.Uniqueness
