-- Prove2me | Theorems.Thm_StengelZeroSum_Supplement_theorem_10
-- name    : StengelZeroSum.Supplement.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:30:31.892275+00:00
-- url     : https://prove2.me/theorems/7b9569b8-9ad1-4f34-b17d-7bbb413b7608
-- title:
--   Theorem 10 (Conforti–Di Summa–Zambelli) — minimally infeasible $Ax\le b$ has minimally infeasible $Ax=b$, and (78)
-- statement:
--   Let $A$ be a real $m\times n$ matrix ($m,n\ge1$) with rows $a_1,\dots,a_m$, and let $b\in\mathbb R^m$. Suppose the system $Ax\le b$ is **minimally infeasible**: it has no solution, but omitting any one inequality makes it feasible. Then:
--
--   1. the system of equations $Ax=b$ is minimally infeasible: it has no solution, but omitting any one equation makes it feasible;
--   2. reversing any inequality $a_ix\le b_i$ creates a feasible system:
--
--   $$
--   \forall i\in[m]\ \ \exists x^{(i)}\in\mathbb R^n:\ \ a_ix^{(i)}>b_i,\quad \forall k\in[m]-\{i\}:\ a_kx^{(i)}=b_k . \tag{78}
--   $$
--
--   Together with Lemma 1, this gives the paper's short proof of the Lemma of Farkas in its inequality version (15).
--
--   **Formalization Note** "$Ax\le b$ is minimally infeasible" is the published `MatousekLP.Duality.IsMinimallyInfeasible`, which is the paper's definition (p.26); "$Ax=b$ is minimally infeasible" is `IsMinimallyInfeasibleEq`.
--
--   Differences from the source:
--   - reading: the theorem prints $b\in\mathbb R^n$ → `b : Fin m → ℝ` ($b\in\mathbb R^m$); reason: typo; $b$ has one entry $b_i$ for each row $a_i$, $i\in[m]$, of the system $Ax\le b$, which is only well formed for $b\in\mathbb R^m$.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Theorem 10, eq. (78), p.26 (definition of minimally infeasible, p.26; proof pp.26–27)

import Mathlib
import Definitions.Def_MatousekLP_Duality_MinimallyInfeasible
import Definitions.Def_StengelZeroSum_Supplement_IsMinimallyInfeasibleEq

open Matrix MatousekLP.Duality

namespace StengelZeroSum.Supplement

/-- **Theorem 10 (Conforti, Di Summa, and Zambelli)**, von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, Theorem 10, eq. (78), p.26:
"Let `A ∈ ℝ^{m×n}` and `b ∈ ℝ^n` [read: `ℝ^m`] and let `a_1, …, a_m` be the rows of `A`.
Suppose the system `Ax ≤ b` is minimally infeasible. (i) Then the system `Ax = b` is
minimally infeasible. (ii) Reversing any inequality `a_i x ≤ b_i` in `Ax ≤ b` creates a
feasible system: `∀ i ∈ [m] ∃ x^(i) ∈ ℝ^n : a_i x^(i) > b_i, ∀ k ∈ [m] − {i} : a_k x^(i) = b_k`."

**Formalization Note** The printed `b ∈ ℝ^n` is a typo: `b` has one entry `b_i` per row `a_i`,
so `b : Fin m → ℝ`. "`Ax ≤ b` minimally infeasible" is the published
`MatousekLP.Duality.IsMinimallyInfeasible` (the paper's definition, p.26), "`Ax = b` minimally
infeasible" is `IsMinimallyInfeasibleEq`. Rows `[m]` are `Fin m`. `0 < m`, `0 < n` are the
standing assumption (p.4). -/
theorem theorem_10 {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (h : IsMinimallyInfeasible A b) :
    IsMinimallyInfeasibleEq A b ∧
      ∀ i : Fin m, ∃ x : Fin n → ℝ, b i < (A *ᵥ x) i ∧ ∀ k : Fin m, k ≠ i → (A *ᵥ x) k = b k := by sorry

end StengelZeroSum.Supplement
