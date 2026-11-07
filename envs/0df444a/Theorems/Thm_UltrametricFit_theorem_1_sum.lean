-- Prove2me | Theorems.Thm_UltrametricFit_theorem_1_sum
-- name    : UltrametricFit.theorem_1_sum
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:43.986814+00:00
-- url     : https://prove2.me/theorems/d04e2e27-6a76-4d01-8484-eb9b4d4a9455
-- title:
--   Proof of Theorem 1, p.15 — the output against the LP cost
-- statement:
--   Let $x$ be feasible, $\delta\in(0,1/2)$, $p\ge1$, and $U$ an output of a run of Merge($\delta$) on $x$. Then
--   $$\Bigl(\sum_{i<j}|U(i,j)-X(i,j)|^p\Bigr)^{1/p}\le\Gamma\,\Bigl(\sum_{i<j}\mathrm{lp\text{-}cost}_p(x,i,j)\Bigr)^{1/p}.$$
--   The rounding therefore loses at most a factor $\Gamma$ against the LP objective.
--
--   Differences from the source:
--   - generalization: $x$ an optimal solution of the LP (§3) → $x$ any feasible point; reason: optimal solutions are feasible, so the page's case is included
--   - encoding: Algorithm 1 with unspecified merge order → a relation `IsRun` with a universal quantifier over runs, and a relational output `IsOutput`; reason: the paper fixes no order (and §5 speaks of the worst one), so every order is an execution of the algorithm
--   - encoding: $X, U, x_\ell$ are functions on unordered pairs → symmetric functions on `Fin n × Fin n`, with sums over $i<j$ and diagonals never read; reason: Lean convention; same instances
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), proof of Theorem 1, p.15

import Mathlib
import Definitions.Def_UltrametricFit_IsInstance
import Definitions.Def_UltrametricFit_IsFeasible
import Definitions.Def_UltrametricFit_IsRun
import Definitions.Def_UltrametricFit_errLayer

namespace UltrametricFit

/-- **Proof of Theorem 1, the summation**, Charikar, Gao, STOC 2027 submission (manuscript sha256
87af12a2…), p.15: for each feasible `x`, each run on it and each output `U`,
`(Σ_{i,j} |U(i, j) − X(i, j)|^p)^{1/p} ≤ Γ · (Σ_{i,j} lp-cost_p(x, i, j))^{1/p}`, with `(i, j)` over
`([n] choose 2)`. -/
theorem theorem_1_sum {n : ℕ} (X : Fin n → Fin n → ℝ) (hX : IsInstance X)
    (x : ℕ → Fin n → Fin n → ℝ) (hx : IsFeasible X x) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (p : ℝ) (hp : 1 ≤ p) (C : ℕ → Finset (Finset (Fin n)))
    (M : ℕ → List (Finset (Fin n) × Finset (Fin n))) (hrun : IsRun X x δ C M)
    (U : Fin n → Fin n → ℝ) (hU : IsOutput X C U) :
    lpDist p U X ≤ Gamma δ p * lpCost X p x ^ (1 / p) := by sorry

end UltrametricFit
