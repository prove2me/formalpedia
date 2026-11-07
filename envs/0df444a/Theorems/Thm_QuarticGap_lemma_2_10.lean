-- Prove2me | Theorems.Thm_QuarticGap_lemma_2_10
-- name    : QuarticGap.lemma_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:37.508406+00:00
-- url     : https://prove2.me/theorems/d307eab5-1f6b-4a88-bdcc-7e55b6dd3722
-- title:
--   Lemma 2.10 — reduction from unstructured search: a sampler with error $\varepsilon < p_*$ needs $\Omega(\sqrt n)$ queries
-- statement:
--   Fix a sampling task whose inputs contain $A(\emptyset)$ and $A(a)$ for $a$ in a set of size $n-1$, with an injective map $a \mapsto j(a)$ into the outcomes and a constant $p_* > 0$, such that
--
--   1. every coherent input operation on these inputs can be implemented with $O(1)$ queries to the bit oracle of a string $s \in \{0,1\}^{n-1}$, where $s = 0$ for $A(\emptyset)$ and $s$ is the indicator vector of $a$ for $A(a)$;
--   2. for every $a$, the target distribution of $A(a)$ assigns probability at least $p_*$ to $j(a)$.
--
--   Then every quantum algorithm that solves the sampling task with a constant error $\varepsilon < p_*$ makes $\Omega(\sqrt n)$ queries on some of these inputs, for all sufficiently large $n$.
--
--   All quantum lower bounds of the paper follow from this reduction.
--
--   **Formalization Note** The $O(1)$ constant, $p_*$ and $\varepsilon$ come first, and the $\Omega$ constant and the threshold depend only on them. `Legal` is the set of legal choices of the operations of each input.
--
--   Differences from the source:
--   - encoding: a family of inputs and a set of size n − 1 → an abstract set Legal of oracle tuples for each input, and a set marks of d-bit strings with n = |marks| + 1; reason: the lemma is stated once for all families
--   - reading: a quantum algorithm → an oracle circuit over all unitary gates, on any number of wires, measured at the end, with any output map; reason: Definition 2.2 grants controlled versions, so measurements can be deferred at no cost in queries
--   - encoding: the target distribution of an input → a nonnegative vector summing to one, as a hypothesis; reason: Lean takes it as a free function
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), Lemma 2.10, p.20

import Mathlib
import Definitions.Def_QuarticGap_IsCoherentAccess

open QAlgorithms

namespace QuarticGap

/-- Lemma 2.10 (arXiv:2610.42069 (file sha256 9f68aaf9…), p.20). Fix a sampling task whose inputs
contain `A(∅)` and `A(a)` for `a` in a set of size `n − 1`, with an injective map `a ↦ j(a)` into the
outcomes and a constant `p∗ > 0`. Suppose every coherent input operation on these inputs can be
implemented with `O(1)` queries to the bit oracle of `s` (`s = 0` for `A(∅)`, the indicator of `a` for
`A(a)`), and that the target of `A(a)` gives `j(a)` probability at least `p∗`. Then every quantum
algorithm that solves the task with constant error `ε < p∗` makes `Ω(√n)` queries on these inputs.

**Formalization Note** The `O(1)` constant `C₀`, `p∗` and `ε` come first; `c`, `n₀` depend on nothing
else ("for every sufficiently large n"). `Legal inp orc` says that `orc` is a choice of the input
operations of input `inp`. The simulation's `orc` is one of them, and the algorithm must succeed on
every legal choice (Definition 2.2). Positions are a set `marks` of `d`-bit strings, of any size,
`n = |marks| + 1`. Query count is the total of a fixed circuit. Targets are probability vectors. -/
theorem lemma_2_10 (C₀ : ℕ) (pstar ε : ℝ) (hp : 0 < pstar) (hε : 0 ≤ ε) (hεp : ε < pstar) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ {r : ℕ} (a : Fin r → ℕ) (d : ℕ) (marks : Finset (Qubits d))
      {Y : Type} [Fintype Y] [DecidableEq Y]
      (Legal : Option marks → ((k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) → Prop)
      (target : Option marks → Y → ℝ) (j : marks ↪ Y) (t : ℕ) (sim : AccessSim a (d + 1) t),
      n₀ ≤ marks.card + 1 →
      sim.CallsAtMost C₀ →
      (∀ inp, ∃ orc, Legal inp orc ∧ sim.Realizes (bitOracle (searchString inp)) orc) →
      (∀ inp y, 0 ≤ target inp y) → (∀ inp, ∑ y, target inp y = 1) →
      (∀ b : marks, pstar ≤ target (some b) (j b)) →
      ∀ (N : ℕ) (alg : OracleCircuit UnitaryGates a N) (out : Qubits N → Y),
        (∀ inp orc, Legal inp orc → tv (qOut alg orc out) (target inp) ≤ ε) →
        c * Real.sqrt (marks.card + 1) ≤ totalQueries alg := by sorry

end QuarticGap
