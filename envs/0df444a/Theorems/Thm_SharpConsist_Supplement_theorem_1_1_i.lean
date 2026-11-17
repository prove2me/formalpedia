-- Prove2me | Theorems.Thm_SharpConsist_Supplement_theorem_1_1_i
-- name    : SharpConsist.Supplement.theorem_1_1_i
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:23:17.290954+00:00
-- url     : https://prove2.me/theorems/f39dab50-8f50-4e0a-9294-f4c3f6e52b65
-- title:
--   Theorem 1.1(i) — a $(2-\sqrt2-\varepsilon)$-approximation with $O(|X_t|k)$ queries, polynomial arithmetic and $O(\varepsilon^{-2})$ recourse
-- statement:
--   Let $\beta=2-\sqrt2$. Elements arrive one at a time; $X_t$ is the set of the first $t$ arrivals, $S_t\subseteq X_t$ the maintained set ($S_0=\emptyset$), and $\mathrm{OPT}_k(X_t)=\max\{f(O):O\subseteq X_t,|O|\le k\}$.
--
--   There are absolute constants $C,K>0$ such that for every $\varepsilon\in(0,\beta)$ there is a randomized value-oracle algorithm, a program of the counted real-RAM oracle machine, and a polynomial bound $c\,(t+k+1)^d$ with the following properties, for every stream with a normalized monotone submodular objective $f$, every capacity $k\ge1$ and every arrival $t$:
--
--   1. on every outcome of the randomness, arrival $t$ ends within $c\,(t+k+1)^d$ steps (value queries, arithmetic operations, comparisons and draws) and makes at most $C\,|X_t|\,k$ value queries;
--   2. on every outcome, $|S_t|\le k$ and
--   $$|S_t\triangle S_{t-1}|\le K\varepsilon^{-2};$$
--   3. $S_t$ is a random variable and
--   $$\mathbb E f(S_t)\ \ge\ (\beta-\varepsilon)\,\mathrm{OPT}_k(X_t).\tag{1.1}$$
--
--   The algorithm knows neither the stream length nor the future elements, and the instance is fixed before its randomness. Part (ii) of Theorem 1.1, the goal of this mission, shows that $\beta$ cannot be improved with $e^{o(k)}$ queries and $o(k)$ recourse.
--
--   Differences from the source:
--   - encoding: a finite ground set V whose elements arrive one at a time; X_t the first t arrivals → V = Fin N with element i the (i+1)-st arrival, X_t = {0, …, t−1}, objectives read on sets of arrival indices (natFn), OPT_k(X_t) = optAt k F t; reason: the algorithm sees the objective only through its values, so naming elements by arrival index changes no instance
--   - reading: a randomized value-oracle algorithm with unit-cost queries, exact arithmetic and exact sampling (§2.1, p.4), performing polynomially many arithmetic operations → a program of OracleRAM: the published SmaleNinth real pointer RAM (exact + − × ÷, comparisons, pointers, no floor) with a Uniform[0,1] tape, a value-query instruction on a set marked in memory, and a halt-with-output instruction; rational literals; every executed instruction costs one step and the per-call step count is bounded by c(·+·+1)^d; reason: the page fixes the cost model only in words; this is the standard real RAM of that description; rational literals and the step bound on every tape only restrict the algorithm
--   - reading: O(|X_t|k) current value queries per arrival and O(ε^{-2}) recourse → query bound C·t·k and recourse bound K/ε² with C, K > 0 fixed before ε (uniform in ε, the stream, k and t); reason: the stronger reading of O(·); the proof gives (2κ+1)|X| greedy queries and 8⌈3/ε⌉²+2 recourse, both of this form
--   - encoding: bounds for every outcome of the randomness; almost-sure termination after every arrival → query, capacity and recourse bounds (and termination within the budget) required for every seed; reason: worst case over seeds as on the page; requiring it on null sets too only restricts the algorithm
--   - encoding: E f(S_t), an expectation over the algorithm's randomness → the conclusion also asserts that {ω | S_t(ω) = S} is measurable for every S, and the expectation is the integral over the seed (tape) law; reason: makes the expectation genuine; it only adds to what the algorithm must satisfy
--   - encoding: integer capacity k ≥ 1 (p.1) → hypothesis 1 ≤ k; reason: the model's standing assumption
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §1.1, Theorem 1.1(i), Eq. (1.1), p.2; §2.1, p.4; proof p.12

import Mathlib
import Definitions.Def_PolyContract_IsRankFunction
import Definitions.Def_SharpConsist_Supplement_natFn
import Definitions.Def_SharpConsist_Supplement_optAt
import Definitions.Def_SharpConsist_Supplement_OracleRAM

namespace SharpConsist.Supplement

open SharpConsist.Supplement.OracleRAM

/-- **Theorem 1.1(i) (algorithmic guarantee).** Fu–Zhang–Tao, *A Sharp Barrier of Consistent
Submodular Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…), §1.1, Theorem 1.1(i),
Eq. (1.1), p.2; model §1, p.1 and §2.1, p.4. `β = 2 − √2`.

There are absolute constants `C, K > 0` such that for every `ε ∈ (0, β)` there is one program `P` of
the counted real-RAM oracle machine (rational literals) and a polynomial bound `c (t + k + 1)^d` with
the following property. On every stream `V = Fin N` with a normalized monotone submodular objective
`f`, every capacity `k ≥ 1` and every outcome `ω` of the uniform tape: every arrival `t ≤ N` ends
within `c (t + k + 1)^d` machine steps (value queries, arithmetic operations, comparisons and draws),
it makes at most `C · t · k = C |X_t| k` value queries, and the maintained set satisfies
`|S_t| ≤ k` and `|S_t △ S_{t−1}| ≤ K ε⁻²`; moreover, for every `t`, `S_t` is a random variable and
`E f(S_t) ≥ (β − ε) OPT_k(X_t)`.

**Formalization Note.** Elements are arrival indices (`natFn`), `X_t = {0, …, t − 1}`, `S_0 = ∅`.
`O(|X_t| k)` and `O(ε⁻²)` are read with constants fixed before `ε`. The program sees neither `N` nor
future elements; the instance is chosen after the program. -/
theorem theorem_1_1_i :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < 2 - Real.sqrt 2 →
      ∃ (P : Program) (c d : ℕ), Admissible P ∧
        ∀ (N : ℕ) (f : Finset (Fin N) → ℝ), PolyContract.IsRankFunction f →
        ∀ k : ℕ, 1 ≤ k →
          (∀ ω : ℕ → unitInterval, ∃ s h,
            runOnline P (natFn f) k (fun t => c * (t + k + 1) ^ d) ω N = some (s, h) ∧
            ∀ t : ℕ, 1 ≤ t → t ≤ N →
              (queriesAt h t : ℝ) ≤ C * (t : ℝ) * (k : ℝ) ∧ (outputAt h t).card ≤ k ∧
              ((symmDiff (outputAt h t) (outputAt h (t - 1))).card : ℝ) ≤ K / ε ^ 2) ∧
          ∀ t : ℕ, 1 ≤ t → t ≤ N →
            (∀ S : Finset ℕ,
              MeasurableSet {ω | outAt P (natFn f) k (fun t => c * (t + k + 1) ^ d) ω t = S}) ∧
            (2 - Real.sqrt 2 - ε) * optAt k (natFn f) t ≤
              ∫ ω, natFn f (outAt P (natFn f) k (fun t => c * (t + k + 1) ^ d) ω t) ∂tape := by sorry

end SharpConsist.Supplement
