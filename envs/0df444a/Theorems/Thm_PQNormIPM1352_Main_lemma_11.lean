-- Prove2me | Theorems.Thm_PQNormIPM1352_Main_lemma_11
-- name    : PQNormIPM1352.Main.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:28.709423+00:00
-- url     : https://prove2.me/theorems/61fc30fc-0a89-4120-b15d-cb6848b024f0
-- title:
--   Lemma 11 — Algorithm 4 returns a $\delta$-approximate Newton step in expected time $\tilde O(s\log(1/\delta))$
-- statement:
--   Fix solver-contract constants $c_0, k_0$. There are constants $C$ and $k$, depending only on $c_0, k_0$, such that the following holds for every SDD-solver oracle meeting the contract of Theorem 2 with $c_0, k_0$. Let $p\ge q>1$, let the support $S$ ($s$ entries) have no all-zero row or column, let $a\in\mathbb R^s$ be the entry values, let $x=(z,y,\gamma)\in\mathrm{int}(K)$, $H = \nabla^2F(x)$, $0<\delta<1$ and $\eta>0$. Let $\Delta = -H^{-1}\nabla\Phi_\eta(x)$ be the Newton step of $\Phi_\eta = F + \eta\langle-\bar a,\cdot\rangle$ and $\tilde\Delta$ the output of Algorithm 4. Then, on every random outcome,
--   $$\|\tilde\Delta - \Delta\|_H \le \delta\,\|\Delta\|_H,$$
--   and the expected cost of Algorithm 4 is at most
--   $$C\,(s+1)\,\log(m+n+s+2)^k\,\big(1 + \log(1/\delta)\big).$$
--
--   With $\delta = \Theta(1)$ each interior-point iteration therefore costs $\tilde O(s)$.
--
--   **Formalization Note** Costs are those of the mission's cost model, with the oracle's costs bounded by the contract. The constants are quantified before the oracle and all instance data.
--
--   Differences from the source:
--   - encoding: the non-negative matrix after removing all-zero rows and columns, a standing assumption of §3 (p. 7) → a sparsity pattern with every row and column occupied (`Preprocessed`) and the barrier on ℝ^{m+n+s}; reason: the paper removes such rows and columns before (5) and works with the support S only
--   - generalization: STSolve of Theorem 2 → every solver oracle meeting the contract of Theorem 2 with constants c₀, k₀; reason: the lemma uses only the contract (10)–(11) and the running time of Theorem 2; STSolve is one such oracle
--   - generalization: a matrix A with s non-zero entries → arbitrary entry values a ∈ ℝ^s on the pattern; reason: the values enter only the gradient; the proof does not use that they are non-zero
--   - reading: Õ(s log(1/δ)) → C(s+1) log(m+n+s+2)^k (1 + log(1/δ)) with C, k depending only on c₀, k₀; reason: Õ hides polylog(m, n, s) (§2.1); the additive 1 keeps the bound valid as δ → 1, where log(1/δ) → 0 but the cost is at least linear in s
--   - encoding: ∥Δ̃ − Δ∥_H ≤ δ∥Δ∥_H and “computed in time …” → the bound for every outcome in the support of the run, and the time as expected cost; reason: the randomness is the solver's; Theorem 2's guarantee holds for every outcome and its time in expectation
-- source:
--   Marco Pirazzini, Daniel Spielman, A Fast and Accurate Algorithm for the p → q Norm of Sparse Non-Negative Matrices, STOC 2027 submission #1352 (October 2026), Lemma 11, printed p. 17 (PDF p. 18); Algorithms 2–4, pp. 16–17; Theorem 2, p. 4

import Mathlib
import Definitions.Def_PQNormIPM1352_Main_Barrier
import Definitions.Def_PQNormIPM1352_Main_NewtonSolve

namespace PQNormIPM1352.Main

/-- **Lemma 11** (Pirazzini–Spielman, STOC 2027 #1352, p. 17). For every pair of solver-contract
constants `c₀, k₀` there are constants `C, k` such that the following holds for every solver
oracle meeting the contract of Theorem 2 with `c₀, k₀`. Let `p ≥ q > 1`, a preprocessed pattern
with `s` entries and values `a`, `x = (z, y, γ) ∈ int(K)`, `H = ∇²F(x)`, `0 < δ < 1` and `η > 0`;
let `Δ = −H⁻¹ ∇Φ_η(x)` be the Newton step of `Φ_η = F + η⟨−ā, ·⟩`. Every output `Δ̃` of Algorithm 4
satisfies `‖Δ̃ − Δ‖_H ≤ δ ‖Δ‖_H`, and its expected cost is at most
`C (s + 1) log(m + n + s + 2)^k (1 + log(1/δ))`. -/
theorem lemma_11 : ∀ c₀ k₀ : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ S : Solver, SatisfiesContract S c₀ k₀ →
    ∀ {m n s : ℕ} (P : SparsePattern m n s), P.Preprocessed →
    ∀ (a : Fin s → ℝ) (p q : ℝ), 1 < q → q ≤ p →
    ∀ x ∈ interior (P.setK p q), ∀ δ η : ℝ, 0 < δ → δ < 1 → 0 < η →
      (∀ o ∈ (run S (newtonSolve m n s P.rowFn P.colFn (finArr a) p q δ η (finArr x))).support,
        localNorm (P.barrierF p q) x
            (arrVec (m + n + s) o.1 - newtonStep (penalized (P.barrierF p q) (P.cvec a) η) x) ≤
          δ * localNorm (P.barrierF p q) x
            (newtonStep (penalized (P.barrierF p q) (P.cvec a) η) x)) ∧
      expectedCost S (newtonSolve m n s P.rowFn P.colFn (finArr a) p q δ η (finArr x)) ≤
        ENNReal.ofReal (C * (s + 1) * Real.log (m + n + s + 2) ^ k * (1 + Real.log (1 / δ))) := by sorry

end PQNormIPM1352.Main
