-- Prove2me | Theorems.Thm_PQNormIPM1352_Main_lemma_7
-- name    : PQNormIPM1352.Main.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:01.805346+00:00
-- url     : https://prove2.me/theorems/b1086d2c-1b03-4736-83c1-0effdc3210f1
-- title:
--   Lemma 7 — the analytic center $x_0$ minimizes (6) and is computed in $O(s)$
-- statement:
--   Let $p \ge q > 1$ and let the support $S$ ($s$ entries) have no all-zero row or column, with row degrees $d_i$ and column degrees $e_j$. Define $x_0 = (z_0, y_0, \gamma_0)$ by
--   $$z_0(i) = \frac{(1 + 1/q^*)\,d_i}{1 + (1 + 1/q^*)\,s},\qquad y_0(j) = \frac{(1 + 1/p)\,e_j}{1 + (1 + 1/p)\,s},\qquad \gamma_0(i,j) = 0.$$
--   Then:
--   1. $x_0 \in \mathrm{int}(K)$, $F(x_0) \le F(x)$ for every $x \in \mathrm{int}(K)$, and $x_0$ is the only point of $\mathrm{int}(K)$ where this minimum is attained (so $x_0$ is *the* minimizer of the barrier (6));
--   2. $x_0$ can be computed in time $O(s)$: there is a universal constant $C$ such that, for every instance and every solver oracle, the program `initProg` (Steps 5–6 of Algorithm 1) returns exactly $x_0$ at cost at most $C\,(s+1)$.
--
--   The analytic center is the starting point of the interior-point method; its closed form makes initialization linear-time.
--
--   **Formalization Note** The cost is that of the mission's cost model; `initProg` uses no oracle call, so its run is deterministic. The constant $C$ is quantified before all instance data. Since the pattern is preprocessed, $m, n \le s$, and loops over rows and columns are within the $O(s)$ bound.
--
--   Differences from the source:
--   - encoding: the non-negative matrix after removing all-zero rows and columns, a standing assumption of §3 (p. 7) → a sparsity pattern with every row and column occupied (`Preprocessed`) and the barrier on ℝ^{m+n+s}; reason: the paper removes such rows and columns before (5) and works with the support S only
--   - reading: “the minimizer for the self-concordant barrier (6)”, F : int(K) → ℝ → x₀ ∈ int(K), F(x₀) ≤ F(x) on int(K), and x₀ is the unique point of int(K) attaining the minimum; reason: the definite article asserts uniqueness; F is defined on int(K) only
--   - encoding: “computed in time O(s)” → ∃ universal C, the program initProg returns x₀ at cost ≤ C(s+1) on every run; reason: O(·) with an explicit universal constant in the mission's cost model
-- source:
--   Marco Pirazzini, Daniel Spielman, A Fast and Accurate Algorithm for the p → q Norm of Sparse Non-Negative Matrices, STOC 2027 submission #1352 (October 2026), Lemma 7, printed p. 9 (PDF p. 10)

import Mathlib
import Definitions.Def_PQNormIPM1352_Main_Barrier
import Definitions.Def_PQNormIPM1352_Main_Algorithm1

namespace PQNormIPM1352.Main

/-- **Lemma 7** (Pirazzini–Spielman, STOC 2027 #1352, p. 9). For `p ≥ q > 1` and a preprocessed
sparsity pattern, the point `x₀ = (z₀, y₀, γ₀)` with
`z₀(i) = (1 + 1/q*) dᵢ / (1 + (1 + 1/q*) s)`, `y₀(j) = (1 + 1/p) eⱼ / (1 + (1 + 1/p) s)`, `γ₀ = 0`
is the minimizer of the barrier (6) over `int(K)` (it lies in `int(K)`, attains the minimum, and
is the only point that does), and it is computed in time `O(s)`: the program `initProg` (Steps
5–6 of Algorithm 1) returns exactly `x₀` at cost `≤ C (s + 1)` for a universal constant `C`. -/
theorem lemma_7 : ∃ C : ℝ, ∀ (S : Solver) {m n s : ℕ} (P : SparsePattern m n s),
    P.Preprocessed → ∀ p q : ℝ, 1 < q → q ≤ p →
      (P.initPoint p q ∈ interior (P.setK p q) ∧
        (∀ x ∈ interior (P.setK p q), P.barrierF p q (P.initPoint p q) ≤ P.barrierF p q x) ∧
        (∀ x ∈ interior (P.setK p q),
          P.barrierF p q x = P.barrierF p q (P.initPoint p q) → x = P.initPoint p q)) ∧
      ∀ o ∈ (run S (initProg m n s P.rowFn P.colFn p q)).support,
        (∀ i : Fin (m + n + s), o.1 i = P.initPoint p q i) ∧ (o.2 : ℝ) ≤ C * (s + 1) := by sorry

end PQNormIPM1352.Main
