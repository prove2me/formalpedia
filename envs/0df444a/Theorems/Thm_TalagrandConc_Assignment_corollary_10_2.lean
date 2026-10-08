-- Prove2me | Theorems.Thm_TalagrandConc_Assignment_corollary_10_2
-- name    : TalagrandConc.Assignment.corollary_10_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:03.71098+00:00
-- url     : https://prove2.me/theorems/3caa26b1-f230-4048-b20b-0ecf6463de91
-- title:
--   Corollary 10.2 — if D_u is α-expanding, an optimal assignment uses only costs ≤ 4muN⁻¹log N
-- statement:
--   Let $X = (X_{i,j})_{i \in I, j \in J}$ be a cost matrix with entries in $[0,1]$, $|I| = |J| = N$, let $u > 0$, and let $D_u = \{(i,j) ;\ X_{i,j} \le 2uN^{-1}\log N\}$. Assume $D_u$ is $\alpha$-expanding and let $m \ge 1$ be an integer with $\alpha^m \ge N/2$. Then every optimal assignment $\tau$ satisfies
--   $$X_{i,\tau(i)} \le 4 m u N^{-1} \log N \qquad \text{for all } i \in I.$$
--
--   This is what allows the costs $X_{i,j}$ to be replaced by truncated costs $\min(X_{i,j}, v)$ with $v = 4muN^{-1}\log N$ without changing the optimal cost, on the event that $D_u$ is expanding.
--
--   **Formalization Note** The statement is deterministic in the cost matrix (it holds for every realization with entries in $[0,1]$, the support of the uniform law). "Optimal" means of minimal cost among all permutations. As in Lemma 10.1, $m \ge 1$ is added; with $m = 0$ (so $N \le 2$) the bound would read $X_{i,\tau(i)} \le 0$, which fails.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 167, Corollary 10.2

import Mathlib
import Definitions.Def_TalagrandConc_Assignment_Basic

namespace TalagrandConc.Assignment

/-- Talagrand (1995), p. 167, Corollary 10.2. If the digraph `D_u` of the cost matrix
`X` (entries in `[0, 1]`) is `α`-expanding and `m ≥ 1` is an integer with `α^m ≥ N/2`,
then every optimal assignment `τ` satisfies `X_{i,τ(i)} ≤ 4 m u N⁻¹ log N` for all `i`. -/
theorem corollary_10_2 {N : ℕ} (X : Fin N × Fin N → ℝ) (hX : ∀ p, X p ∈ Set.Icc (0 : ℝ) 1)
    (u : ℝ) (hu : 0 < u) (α : ℝ) (hD : IsExpanding N α (digraphU N u X))
    (m : ℕ) (hm : 1 ≤ m) (hαm : (N : ℝ) / 2 ≤ α ^ m)
    (τ : Equiv.Perm (Fin N)) (hτ : IsOptimalAssignment X τ) (i : Fin N) :
    X (i, τ i) ≤ 4 * m * u * (N : ℝ)⁻¹ * Real.log N := by sorry

end TalagrandConc.Assignment
