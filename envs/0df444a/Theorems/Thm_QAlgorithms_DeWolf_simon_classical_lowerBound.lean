-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_simon_classical_lowerBound
-- name    : QAlgorithms.DeWolf.simon_classical_lowerBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:34:07.11887+00:00
-- url     : https://prove2.me/theorems/420d3b3a-7117-4793-8940-ad270eaed58f
-- title:
--   Classical randomized lower bound Ω(√(2^n)) for decision Simon
-- statement:
--   This is the classical query lower bound for the decision version of Simon's problem.
--
--   Let $N=2^n$, identify indices with $\{0,1\}^n$, and let an input be $x=(x_i)_{i\in\{0,1\}^n}$ with $x_i\in\{0,1\}^n$. The promise is that some $s\in\{0,1\}^n$ (now $s=0^n$ is allowed) satisfies $x_i=x_j\iff(i=j\text{ or } i=j\oplus s)$; the task is to decide whether $s=0^n$. A classical randomized $T$-query algorithm is a probability distribution over deterministic adaptive decision trees, each of which queries indices $i$, receives the whole string $x_i$, makes at most $T$ queries on every input, and outputs a bit.
--
--   There are constants $c>0$ and $n_0$ such that for every $n\ge n_0$ and every randomized $T$-query algorithm $R$: if for every input $x$ satisfying the promise with string $s$,
--
--   $$
--   \Pr\big[R(x)=[s=0^n]\big]\ge \tfrac23,
--   $$
--
--   then
--
--   $$
--   T\ge c\sqrt{2^n}.
--   $$
--
--   Combined with Simon's quantum algorithm, this is the first proven exponential separation between quantum and bounded-error classical query complexity.
--
--   **Formalization Note** The string $s$ in the promise is unique for each promised input, so the success condition is quantified over all pairs $(x,s)$ satisfying the promise. The bound is stated for worst-case success $\ge 2/3$ on every promised input (the standard notion of computing with bounded error, p.26); the source's proof argues under a distribution $\mu$, which this hypothesis implies.
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, PDF p. 37, §3.3.2. https://homepages.cwi.nl/~rdewolf/qcnotes.pdf

import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QAlgorithms_DeWolf_Ch03_Model
set_option autoImplicit false

namespace QAlgorithms.DeWolf




/-- de Wolf §3.3.2 (PDF pp. 37–38), the classical lower bound for the decision version of
Simon's problem (where `s = 0^n` is also allowed; task: decide whether `s = 0^n`). There are
constants `c > 0` and `n₀` such that for every `n ≥ n₀`, every classical randomized algorithm
(a probability distribution over deterministic adaptive decision trees, each querying whole
strings `x_i` and making at most `T` queries on every input) that, on every input `x` satisfying
the promise with some `s`, outputs the answer `[s = 0^n]` with probability at least `2/3`, makes
`T ≥ c √(2^n)` queries. -/
theorem simon_classical_lowerBound :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (T : ℕ) (R : RandDecisionTree (Qubits n) (Qubits n) Bool),
      RandMakesAtMost R T →
      (∀ (x : Qubits n → Qubits n) (s : Qubits n), SimonPromise x s →
        successProb R x (decide (s = 0)) ≥ 2 / 3) →
      c * Real.sqrt ((2 : ℝ) ^ n) ≤ T := by
  sorry

end QAlgorithms.DeWolf
