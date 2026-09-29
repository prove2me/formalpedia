-- Prove2me | Theorems.Thm_Polyhedral_gale_alternative
-- name    : Polyhedral.gale_alternative
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-28T00:35:52.226985+00:00
-- url     : https://prove2.me/theorems/6e772d7d-7b64-455f-bdeb-9e5e9efdf60d
-- title:
--   Gale's theorem of the alternative for Bπ ≤ c
-- statement:
--   **Gale's theorem of the alternative.** Let $B \in \mathbb{R}^{r \times k}$ and $c \in \mathbb{R}^r$. Exactly one of the following holds:
--
--   $$\text{(a)}\quad \exists\, \pi \in \mathbb{R}^k:\ B\pi \le c \qquad\text{or}\qquad \text{(b)}\quad \exists\, w \ge 0:\ B^{\mathsf T} w = 0,\ w^{\mathsf T} c < 0 .$$
--
--   This is the inequality-form companion of Farkas' lemma: a system of linear inequalities is unsolvable precisely when some nonnegative combination of its rows yields the contradiction $0 \le$ (a negative number). It is the transposition theorem behind linear programming duality in inequality form, behind the existence of dual multipliers for a linear program whose primal optimum is known, and behind the characterization of consistent linear inequality systems.
--
--   **Formalization note.** `Xor` is exclusive disjunction, so the statement contains both the incompatibility of the alternatives and the fact that one of them must hold. Vectors are functions out of a `Fin` type, `B.mulVec pi` is $B\pi$, `B\u1d40.mulVec w` is $B^{\mathsf T}w$, and `\u2b1d\u1d65` is the dot product.
-- source:
--   D. Gale, The Theory of Linear Economic Models, McGraw-Hill 1960, Theorem 2.8; see also D. Bertsimas and J. N. Tsitsiklis, Introduction to Linear Optimization, Athena Scientific 1997, Section 4.6

import Mathlib

open Matrix

theorem Polyhedral.gale_alternative {r k : ℕ} (B : Matrix (Fin r) (Fin k) ℝ)
    (c : Fin r → ℝ) :
    Xor (∃ pi : Fin k → ℝ, ∀ i, B.mulVec pi i ≤ c i)
      (∃ w : Fin r → ℝ, (∀ i, 0 ≤ w i) ∧ Bᵀ.mulVec w = 0 ∧ w ⬝ᵥ c < 0) := by sorry
