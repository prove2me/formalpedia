-- Prove2me | Theorems.Thm_VAS5Reach_theorem_3_3
-- name    : VAS5Reach.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:26:24.246308+00:00
-- url     : https://prove2.me/theorems/1ffcf5b4-316d-4801-9942-da3ae658176c
-- title:
--   Theorem 3.3 (Pottier) — minimal solutions satisfy $\|x_0\|_1 \le (1 + \|A\|_{1,\infty} + \|b\|)^{\operatorname{rank}(A\ b)}$
-- statement:
--   Let $Ax = b$ be a linear Diophantine system with $A \in \mathbb Z^{m \times n}$ and $b \in \mathbb Z^m$. Each minimal element $x_0$ (for the componentwise order) of $\{x \in \mathbb N^n \setminus \{0\} : Ax = b\}$ satisfies
--   $$
--   \|x_0\|_1 \le \bigl(1 + \|A\|_{1,\infty} + \|b\|\bigr)^r, \tag{3}
--   $$
--   where $\|A\|_{1,\infty} := \max_{i \in [m]} \|a_i\|_1$ over the rows $a_i$ of $A$, $\|b\|$ is the max norm, and $r := \operatorname{rank}(A\ b)$ is the rank of the augmented matrix. This is [Pot91, Theorem 1]; the proof is in the cited work.
--
--   **Formalization Note** The rank is taken over $\mathbb Q$; $\|A\|_{1,\infty} = 0$ when $m = 0$.
--
--   Differences from the source: none.
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Theorem 3.3, eq. (3), pp.16–17 (PDF pp.18–19); norms p.16; cited from [Pot91, Theorem 1]

import Mathlib
import Definitions.Def_VAS5Reach_supNorm

namespace VAS5Reach

/-- **Theorem 3.3 (Pottier's Theorem [Pot91, Theorem 1]).** Let `Ax = b` be a linear Diophantine
system, where `A ∈ ℤ^{m×n}` and `b ∈ ℤ^m`. Each minimal element `x₀` in `{x ∈ ℕⁿ ∖ {0} : Ax = b}`
satisfies `∥x₀∥₁ ≤ (1 + ∥A∥_{1,∞} + ∥b∥)^r` (3), where `r := rank (A b)` is the rank of the
augmented matrix `(A b)`.

Here `∥A∥_{1,∞} := max_{i∈[m]} ∥aᵢ∥₁` over the rows `aᵢ` of `A`, and `∥b∥` is the max norm.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Theorem 3.3, eq. (3), printed pp. 16–17 (PDF pp. 18–19); `∥A∥_{1,∞}` on printed
p. 16. Cited from [Pot91, Theorem 1]; the proof is not in this paper.

**Formalization Note** "Minimal" is for the componentwise order: `x₀` is a nonzero solution and no
nonzero solution `x ≤ x₀` differs from `x₀`. The rank is over `ℚ`; the augmented matrix has the
column `b` appended as column `n`. `∥A∥_{1,∞} = 0` when `m = 0`. -/
theorem theorem_3_3 (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (x₀ : Fin n → ℕ)
    (hx₀ : x₀ ≠ 0) (hsol : A.mulVec (fun j => (x₀ j : ℤ)) = b)
    (hmin : ∀ x : Fin n → ℕ, x ≠ 0 → A.mulVec (fun j => (x j : ℤ)) = b → x ≤ x₀ → x = x₀) :
    ∑ j, x₀ j ≤ (1 + Finset.univ.sup (fun i => ∑ j, (A i j).natAbs) + supNorm b) ^
      (Matrix.of fun (i : Fin m) (j : Fin (n + 1)) =>
        ((if h : (j : ℕ) < n then A i ⟨j, h⟩ else b i : ℤ) : ℚ)).rank := by sorry

end VAS5Reach
