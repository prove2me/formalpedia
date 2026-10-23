-- Prove2me | Theorems.Thm_SaturatedNet_Uniqueness_proposition_2_iii_v
-- name    : SaturatedNet.Uniqueness.proposition_2_iii_v
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:33.55818+00:00
-- url     : https://prove2.me/theorems/939616cf-73f0-47e0-93f5-a4bd93b8c888
-- title:
--   Proposition 2 (iii)–(v), p. 9 — for irreducible P: positive unique dominant eigenvectors, solvability of ρ(P)x = Pᵀx + c, strict monotonicity
-- statement:
--   Let $P \in \mathbb R_+^{n \times n}$ be nonnegative and *irreducible* (for all $i, j$ some power
--   $P^l$, $l \ge 1$, has $(P^l)_{ij} > 0$), with spectral radius $\rho = \rho(P)$. Then:
--
--   1. **(iii)** every nonnegative nonzero right eigenvector $p$ for $\rho$ ($Pp = \rho p$) has all
--      entries positive, and any other nonnegative nonzero right eigenvector for $\rho$ is a positive
--      multiple of $p$; likewise every nonnegative nonzero left eigenvector $\pi$ ($\pi^\top P = \rho\pi^\top$)
--      is entrywise positive and unique up to a positive factor;
--   2. **(iv)** for every such $p$ and every $c \in \mathbb R^n$ with $p^\top c = 0$, the equation
--      $$\rho(P)\, x = P^\top x + c$$
--      has infinitely many solutions $x \in \mathbb R^n$;
--   3. **(v)** for every proper principal square sub-matrix $Q$ of $P$, $\rho(Q) < \rho(P)$.
--
--   In the paper these facts are used for the irreducible blocks of spectral radius one: (iv) gives the
--   affine line of solutions of $\nu = P^\top \nu + c$ in Proposition 5, (iii) makes the division by
--   $\pi_i$ in (29)–(30) legitimate, and (v) is used to rule out saturated nodes.
--
--   **Formalization Note.** The printed equation in (iv) is $x = \rho(P) P^\top x + c$, which is false
--   when $\rho(P) \ne 1$ (for $P = [2]$, $p = 1$, $c = 0$ it has the single solution $x = 0$); the
--   statement here uses the intended Fredholm form $\rho(P)x = P^\top x + c$, which coincides with the
--   printed one in the case $\rho(P) = 1$, the only one the paper uses. In (v) the empty sub-matrix is
--   allowed (it has spectral radius $0 < \rho(P)$).
-- source:
--   Massai, Como & Fagnani, Equilibria and Systemic Risk in Saturated Networks, arXiv:1912.04815v2, p. 9, Proposition 2 (iii)–(v)

import Mathlib
import Definitions.Def_SaturatedNet_Uniqueness_Model
open Matrix

namespace SaturatedNet.Uniqueness

theorem proposition_2_iii_v {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (hirr : IsIrreducible P) :
    (∀ p : n → ℝ, 0 ≤ p → p ≠ 0 → P *ᵥ p = (specRad P).toReal • p →
      (∀ i, 0 < p i) ∧
      ∀ q : n → ℝ, 0 ≤ q → q ≠ 0 → P *ᵥ q = (specRad P).toReal • q →
        ∃ t : ℝ, 0 < t ∧ q = t • p) ∧
    (∀ π : n → ℝ, 0 ≤ π → π ≠ 0 → π ᵥ* P = (specRad P).toReal • π →
      (∀ i, 0 < π i) ∧
      ∀ σ : n → ℝ, 0 ≤ σ → σ ≠ 0 → σ ᵥ* P = (specRad P).toReal • σ →
        ∃ t : ℝ, 0 < t ∧ σ = t • π) ∧
    (∀ p : n → ℝ, 0 ≤ p → p ≠ 0 → P *ᵥ p = (specRad P).toReal • p →
      ∀ c : n → ℝ, p ⬝ᵥ c = 0 →
        {x : n → ℝ | (specRad P).toReal • x = x ᵥ* P + c}.Infinite) ∧
    (∀ S : Finset n, S ≠ Finset.univ → specRad (block P S) < specRad P) := by sorry

end SaturatedNet.Uniqueness
