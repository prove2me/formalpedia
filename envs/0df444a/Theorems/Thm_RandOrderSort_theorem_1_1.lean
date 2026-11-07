-- Prove2me | Theorems.Thm_RandOrderSort_theorem_1_1
-- name    : RandOrderSort.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:04:57.018768+00:00
-- url     : https://prove2.me/theorems/cd54ed9c-592a-44be-9ca5-4bed15f8fda4
-- title:
--   Theorem 1.1 — one comparison-only online algorithm has ratio $O(\log n)$ with an exponential tail on every fixed multiset
-- statement:
--   There are absolute constants $a_0,a_1,\theta>0$ and a single online algorithm using only comparisons such that, for every $n\ge 2$, every fixed multiset $X$ of $n$ reals and every $z\ge 0$, its output $A$ satisfies
--   $$\mathbb P_{\pi,\sigma}\bigl[\rho(A)>a_0\log n+a_1+z\bigr]\le e^{-\theta z}.$$
--   Here $\pi$ is the uniform arrival order, $\sigma$ is an independent uniform priority permutation that breaks ties, and $\rho(A)$ is the realized competitive ratio of display (1), with natural logarithm. Moreover:
--
--   1. the algorithm completes a legal placement on every execution;
--   2. it is deterministic on distinct inputs: for injective values, its cells do not depend on $\sigma$;
--   3. after generating the priorities, it requires $O(n\log n)$ comparisons and word operations and $O(n)$ auxiliary words.
--
--   Together with the paper's lower bound, Theorem 1.4, this makes the optimal worst-case ratio $\Theta(\log n)$ with high probability.
--
--   **Formalization Note** The constants are chosen before the algorithm and before $n$. The bound on time and space is one program for all $n$, on a word-RAM whose only access to the keys is a comparison of two arrived items.
--
--   Differences from the source:
--   - encoding: a fixed multiset X → x : Fin n → ℝ, with indices distinguishing occurrences; reason: the page's own convention (p.3)
--   - encoding: a single online algorithm using only comparisons → `OnlineCmpAlg`: a rule seeing only n, t and the strict key comparisons among arrivals 0, …, t; reason: this class is no larger than the page's (§3, p.12: "We work with strictly ordered keys"), so the existential is at least as strong
--   - encoding: deterministic on distinct inputs → the cell map does not depend on σ when x is injective; reason: a rule is a function, so it is deterministic for each (π, σ); p.3: "the priorities have no effect when the input values are distinct"
--   - encoding: O(n log n) comparisons and word operations and O(n) auxiliary words → `ImplementsFast`: one program on the online comparison word-RAM, words of c(⌊log₂ n⌋+1) bits, at most Cn(⌊log₂ n⌋+1) steps, at most Cn written memory cells; reason: the paper's cost model (pp.4, 18) as a machine; comparisons are steps, and for n ≥ 2 these bounds are exactly O(n log n) and O(n)
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), Theorem 1.1, p.4, display (2)

import Mathlib
import Definitions.Def_RandOrderSort_OnlineCmpAlg
import Definitions.Def_RandOrderSort_ImplementsFast

namespace RandOrderSort

/-- **Theorem 1.1 (Upper tail in random order)**, Kang, Fan, arXiv:2610.15438 (version of
2026-11-01), p.4: "There are absolute constants a_0, a_1, θ > 0 and a single online algorithm
using only comparisons such that, for every n ≥ 2, every fixed multiset X, and every z ≥ 0, its
output A satisfies P_{π,σ}[ρ(A) > a_0 log n + a_1 + z] ≤ e^{−θz}. (2) The algorithm completes a
legal placement on every execution. It is deterministic on distinct inputs and uses the
independent priority permutation σ to break ties. After generating the priorities, it requires
O(n log n) comparisons and word operations and O(n) auxiliary words."

**Formalization Note.** The constants are chosen before the algorithm and before `n`. The
algorithm is an `OnlineCmpAlg` (it sees only `n`, `t` and the strict key comparisons among the
arrivals so far). Clause by clause: legality for every `n ≥ 2`; the cell map does not depend on
`σ` when the values are distinct; `ImplementsFast` (one online comparison word-RAM program with
`O(log n)`-bit words, `O(n log n)` steps, `O(n)` written words); the tail (2) under the uniform law
of `(π, σ)`, with `log` the natural logarithm. -/
theorem theorem_1_1 :
    ∃ a₀ a₁ θ : ℝ, 0 < a₀ ∧ 0 < a₁ ∧ 0 < θ ∧ ∃ A : OnlineCmpAlg,
      (∀ n, 2 ≤ n → Legal A n) ∧
      (∀ n, 2 ≤ n → ∀ x : Fin n → ℝ, Function.Injective x →
        ∀ π σ σ' : Equiv.Perm (Fin n), cellOf A x π σ = cellOf A x π σ') ∧
      ImplementsFast A ∧
      ∀ n, 2 ≤ n → ∀ x : Fin n → ℝ, ∀ z : ℝ, 0 ≤ z →
        uniformProb (fun ω : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) =>
          a₀ * Real.log n + a₁ + z < ratio A x ω.1 ω.2) ≤ Real.exp (-(θ * z)) := by sorry

end RandOrderSort
