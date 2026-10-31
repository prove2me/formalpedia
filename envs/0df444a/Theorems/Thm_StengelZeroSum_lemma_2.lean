-- Prove2me | Theorems.Thm_StengelZeroSum_lemma_2
-- name    : StengelZeroSum.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:03:33.925785+00:00
-- url     : https://prove2.me/theorems/f9175407-974b-46e4-9680-4a94a0f4314b
-- title:
--   Lemma 2 — basic feasible solutions exist and attain the minimum
-- statement:
--   Let $A$ be a real $m\times n$ matrix, $b\in\mathbb R^m$, $c\in\mathbb R^n$. Call $x$ *basic* if the columns $A_j$ with $x_j\ne0$ are linearly independent.
--
--   1. (a) If $Ax=b$, $x\ge\mathbf 0$ has a feasible solution, then it has a basic feasible solution.
--
--   Suppose moreover that the LP: minimize $c^\top x$ subject to $Ax=b$, $x\ge\mathbf0$ is feasible and has a lower bound $\lambda$, that is, $c^\top x\ge\lambda$ for all feasible $x$. Then
--
--   2. (b) for every feasible $x$ there is a basic feasible solution $x^*$ with $c^\top x^*\le c^\top x$;
--   3. (c) both minima below exist and are equal:
--   $$
--   \min\{c^\top x^*\mid Ax^*=b,\ x^*\ge\mathbf0,\ x^*\text{ basic}\}=\min\{c^\top x\mid Ax=b,\ x\ge\mathbf0\}.
--   $$
--
--   In the paper, (c) supplies the basic minimizer $(z^*,w^*)$ of (58) in Theorem 8, whose size is then bounded through Cramer's rule in Theorem 7(c).
--
--   **Formalization Note** Rows and columns are arbitrary finite types. Each minimum is a least element of the corresponding set of objective values.
--
--   Differences from the source:
--   - generalization: A ∈ ℝ^{m×n} with m, n positive → A indexed by arbitrary finite types (possibly empty); reason: Fin m, Fin n with m, n > 0 are instances; the general form is what Theorem 8 applies to the slack form of (58)
--   - encoding: min{…} = min{…} → a common real μ that is the least element of both sets of objective values; reason: the proof of (c) states that both minima exist and are equal
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Lemma 2, p.20

import Mathlib
import Definitions.Def_StengelZeroSum_IsBasic

open Matrix

namespace StengelZeroSum

/-- **Lemma 2** (basic feasible solutions),
von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, Lemma 2,
p.20. Let `A ∈ ℝ^{m×n}`, `b ∈ ℝ^m`, `c ∈ ℝ^n`.

(a) If `Ax = b, x ≥ 0` has a feasible solution, it has a basic feasible solution.

Furthermore, suppose the LP `minimize c⊤x subject to Ax = b, x ≥ 0` is feasible and has a lower
bound `λ` (`c⊤x ≥ λ` for all feasible `x`). Then
(b) for every feasible `x` there is a basic feasible `x*` with `c⊤x* ≤ c⊤x`, and
(c) `min{c⊤x* | Ax* = b, x* ≥ 0, x* basic} = min{c⊤x | Ax = b, x ≥ 0}`: both minima exist and
are equal.

**Formalization Note** Rows and columns are arbitrary finite types (the paper's `Fin m`,
`Fin n` are instances). "Basic" is `IsBasic A x`: the columns `A_j` with `x_j ≠ 0` are
linearly independent (p.19). Each minimum in (c) is an `IsLeast` of the set of objective values,
which asserts that it is attained. -/
theorem lemma_2 {ρ κ : Type*} [Fintype ρ] [Fintype κ] (A : Matrix ρ κ ℝ) (b : ρ → ℝ)
    (c : κ → ℝ) :
    ((∃ x : κ → ℝ, A *ᵥ x = b ∧ 0 ≤ x) →
      ∃ x : κ → ℝ, A *ᵥ x = b ∧ 0 ≤ x ∧ IsBasic A x) ∧
    ∀ lam : ℝ, (∃ x : κ → ℝ, A *ᵥ x = b ∧ 0 ≤ x) →
      (∀ x : κ → ℝ, A *ᵥ x = b → 0 ≤ x → lam ≤ c ⬝ᵥ x) →
      (∀ x : κ → ℝ, A *ᵥ x = b → 0 ≤ x →
        ∃ xs : κ → ℝ, A *ᵥ xs = b ∧ 0 ≤ xs ∧ IsBasic A xs ∧ c ⬝ᵥ xs ≤ c ⬝ᵥ x) ∧
      ∃ μ : ℝ,
        IsLeast {r : ℝ | ∃ xs : κ → ℝ, A *ᵥ xs = b ∧ 0 ≤ xs ∧ IsBasic A xs ∧ r = c ⬝ᵥ xs} μ ∧
        IsLeast {r : ℝ | ∃ x : κ → ℝ, A *ᵥ x = b ∧ 0 ≤ x ∧ r = c ⬝ᵥ x} μ := by sorry

end StengelZeroSum
