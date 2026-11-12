-- Prove2me | Theorems.Thm_PQNormIPM1352_Main_theorem_1
-- name    : PQNormIPM1352.Main.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:10:43.450948+00:00
-- url     : https://prove2.me/theorems/5d3c84ce-e1a1-4d28-86b9-f6e2bb45ac50
-- title:
--   Theorem 1 — $(1-\varepsilon)$-approximation of $\|A\|_{p\to q}$ for non-negative sparse $A$ in expected time $\tilde O(s^{3/2}\log(1/\varepsilon))$
-- statement:
--   Fix solver-contract constants $c_0, k_0$. There are constants $C > 0$ and $k$, depending only on $c_0, k_0$, such that the following holds for every SDD-solver oracle meeting the contract of Theorem 2 with $c_0, k_0$. On input a non-negative matrix $A\in\mathbb R^{m\times n}$ with $s$ non-zero entries (in sparse representation), two numbers $p \ge q \ge 1$ and $\varepsilon > 0$, the algorithm (Algorithm 1 for $q > 1$, the closed form $\|A^\top\mathbf 1\|_{p^*}$ for $q = 1$) returns, on every random outcome, a value $v$ with
--   $$(1-\varepsilon)\,\|A\|_{p\to q} \le v \le \|A\|_{p\to q},$$
--   and its expected running time is at most
--   $$C\,(s+1)^{3/2}\,\log(m+n+s+2)^k\,\Big(1 + \max\big(0, \log(1/\varepsilon)\big)\Big).$$
--
--   This is the paper's main result: a high-accuracy algorithm for the $p\to q$ norm of sparse non-negative matrices, faster than earlier methods when $\varepsilon < 1/\sqrt s$.
--
--   **Formalization Note** Running time is the expected cost in the mission's randomized real-RAM (`Prog`), with the oracle as the only source of randomness; the constants are quantified before the oracle and the input. The cost bound does not grow with $m$ and $n$ beyond the logarithm, since the input is read in sparse form.
--
--   Differences from the source:
--   - generalization: Algorithm 1 with STSolve of Theorem 2 inside Algorithm 3 → every solver oracle meeting the contract of Theorem 2 with constants c₀, k₀; reason: the proof uses only Theorem 2's guarantees; STSolve is one such oracle, and the exact-inverse oracle shows the contract is satisfiable
--   - reading: T = ⌈100√s log(s/ε)⌉ in Step 4 (sufficient only for s ≥ 20 by footnote 4, p. 11) → T = max(⌈100√s log(s/ε)⌉, ⌈21√ν log(7ν/(6εη₀))⌉), ν = 3s+2; reason: footnote 4 defers small s to an unspecified routine; the added term is the count of the proof of Theorem 5 and equals the printed T for s ≥ 16
--   - reading: “a (1 − ε) multiplicative approximation to ‖A‖_{p→q}” → the returned value v satisfies (1 − ε)‖A‖_{p→q} ≤ v ≤ ‖A‖_{p→q}; reason: the usual meaning; the upper bound holds because v = ‖Au‖_q/‖u‖_p for a vector u
--   - reading: expected time Õ(s^{3/2} log(1/ε)) → C(s+1)^{3/2} log(m+n+s+2)^k (1 + max(0, log(1/ε))), C, k depending only on c₀, k₀; reason: Õ hides polylog(m, n, s) (§2.1); the additive term keeps the bound valid for ε ≥ 1, where log(1/ε) ≤ 0
--   - encoding: Algorithm 1 returns the vector u (u = n^{−1/p}1_n if A = 0) → the algorithm returns the value ‖Au‖_q/‖u‖_p, and 0 if A = 0; reason: Theorem 1 asserts an approximation of the norm; the value is computed from u in O(s), and 0 = ‖0‖_{p→q}
--   - encoding: running time (no machine model in the paper) → expected cost in the mission's randomized real-RAM with unit-cost arithmetic, real powers, logarithms and comparisons; reason: the paper fixes no model; the model charges every primitive through its interpreter and has no norm, supremum or inverse primitive
-- source:
--   Marco Pirazzini, Daniel Spielman, A Fast and Accurate Algorithm for the p → q Norm of Sparse Non-Negative Matrices, STOC 2027 submission #1352 (October 2026), Theorem 1, printed p. 1 (PDF p. 2); proof p. 19 (PDF p. 20)

import Mathlib
import Definitions.Def_PQNormIPM1352_Main_Norms
import Definitions.Def_PQNormIPM1352_Main_Sparse
import Definitions.Def_PQNormIPM1352_Main_Algorithm1

namespace PQNormIPM1352.Main

/-- **Theorem 1** (Pirazzini–Spielman, STOC 2027 #1352, p. 1; proof p. 19). For every pair of
solver-contract constants `c₀, k₀` there are constants `C > 0` and `k` such that, for every
SDD-solver oracle meeting the contract of Theorem 2 with `c₀, k₀`, every non-negative matrix
`A ∈ ℝ^{m×n}` with `s` non-zero entries (sparse input), every `p ≥ q ≥ 1` and every `ε > 0`, the
algorithm `pqNorm` (Algorithm 1 for `q > 1`, the closed form `‖Aᵀ1‖_{p*}` for `q = 1`) returns,
on every random outcome, a value `v` with `(1 − ε)‖A‖_{p→q} ≤ v ≤ ‖A‖_{p→q}`, and its expected
cost is at most `C (s + 1)^{3/2} log(m + n + s + 2)^k (1 + max(0, log(1/ε)))`. -/
theorem theorem_1 : ∀ c₀ k₀ : ℕ, ∃ (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ S : Solver, SatisfiesContract S c₀ k₀ →
    ∀ (A : SparseInput) (p q ε : ℝ), 1 ≤ q → q ≤ p → 0 < ε →
      (∀ o ∈ (run S (pqNorm A.entries p q ε)).support,
        (1 - ε) * opNormPQ A.toMatrix p q ≤ o.1 ∧ o.1 ≤ opNormPQ A.toMatrix p q) ∧
      expectedCost S (pqNorm A.entries p q ε) ≤
        ENNReal.ofReal (C * ((A.s : ℝ) + 1) ^ ((3 : ℝ) / 2) *
          Real.log (A.m + A.n + A.s + 2) ^ k * (1 + max 0 (Real.log (1 / ε)))) := by sorry

end PQNormIPM1352.Main
