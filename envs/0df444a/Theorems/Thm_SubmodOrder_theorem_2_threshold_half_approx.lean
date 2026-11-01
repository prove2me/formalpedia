-- Prove2me | Theorems.Thm_SubmodOrder_theorem_2_threshold_half_approx
-- name    : SubmodOrder.theorem_2_threshold_half_approx
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:38:46.567433+00:00
-- url     : https://prove2.me/theorems/f57210ed-6933-4081-9496-54bc4f952b5f
-- title:
--   Theorem 2 — Algorithm 1 is a $(1-\varepsilon)/2$-approximation with $O((n/\varepsilon)\log k)$ queries (corrected: $k = 1$)
-- statement:
--   Consider the maximization of a monotone subadditive set function $f$ with $f(\emptyset)=0$ subject to the cardinality constraint $|S|\le k$, on a ground set $N$ of $n$ elements with a known weak submodular order $\pi$. There is an absolute constant $C$ such that for every $k\ge1$ and every $\varepsilon\in(0,1)$:
--
--   1. Algorithm 1, run with the value oracle of $f$, outputs a set $S$ with $|S|\le k$ and
--   $$
--   f(S)\ \ge\ (1-\varepsilon)\cdot\tfrac12\cdot\mathrm{OPT},\qquad \mathrm{OPT}=\max\{f(T):T\subseteq N,\ |T|\le k\};
--   $$
--   2. Algorithm 1 makes at most
--   $$
--   C\cdot\frac{n\,(1+\log k)}{\varepsilon}
--   $$
--   value-oracle queries.
--
--   Without a submodular order, no algorithm with polynomially many queries achieves better than $n^{-\Omega(1)}$ for monotone subadditive maximization under a cardinality constraint; with a weak submodular order, Algorithm 1 is a $(1-\varepsilon)\frac12$-approximation, and Theorem 3 of the paper shows that $\frac12+\varepsilon$ cannot be beaten with polynomially many queries even under a strong submodular order. The result applies to assortment optimization under mixtures of multinomial logit models with customization and to streaming submodular maximization.
--
--   **Formalization Note** Algorithm 1 is a value-oracle program built from $\pi$, $k$ and $\varepsilon$ only, and its queries are counted along its run against $f$. The constant $C$ is chosen before every other quantity, and the query bound is stated for every $f$.
--
--   Differences from the source:
--   - correction: the loop of Algorithm 1 runs over i ∈ {1, …, ⌈log_{1+ε} k⌉} → i ∈ {1, …, L}, L = numRounds k ε = max(1, ⌈log_{1+ε} k⌉); reason: at k = 1 the printed loop is empty and its "Best of" is undefined; for n = k = 1, f({e}) = 1, the empty output has value 0 < (1 − ε)/2; for k ≥ 2 nothing changes
--   - correction: O(n/ε log k) oracle queries → at most C · n · (1 + log k)/ε queries, natural logarithm, one absolute constant C; reason: the printed bound is 0 at k = 1, yet for n = 2, k = 1 and f the indicator of containing a fixed element, a query-free algorithm outputs a fixed set and fails the guarantee for one of the two choices
--   - reading: l_π(S), r_π(S) (leftmost, rightmost element), undefined for S = ∅, in "π-nested" and "C to the right of A" → the comparisons π b < π a for all b, a in the two sets, which hold vacuously when a set is empty; reason: the paper applies the weak order with B = E(0) = ∅ (proof of Lemma 1, p.20)
--   - generalization: the query bound for monotone subadditive f with a weak submodular order → the query bound for every f : Finset α → ℝ; reason: the count does not use the hypotheses; it specializes to the paper's f
--   - encoding: a ground set N = {1, …, n} indexed by a known order π → a Fintype α with a bijection π : α ≃ Fin n given to the algorithm; reason: relabelling; every finite ground set with every order is covered
--   - encoding: "oracle queries" → OracleProg.queries of the program algorithm1 π k ε run against f; Threshold Add keeps the value of its current set and does not query f(∅) = 0; reason: the paper's counting: one query per scanned element in Threshold Add, the singleton values for τ
--   - encoding: τ = 1/k max_{e∈N} f({e}) → τ = max(0, max_e f({e}))/k; reason: equal for monotone f with f(∅) = 0 on a nonempty ground set; on the empty ground set τ = 0 and OPT = 0
--   - encoding: "Best of {S₁, …, S_L}" → the first set of largest value, compared by the values returned by Threshold Add; reason: these values equal f(S_i) when f(∅) = 0; ties do not affect the guarantee
--   - encoding: (1−ε)0.5 approximate → f(S) ≥ (1 − ε) · (1/2) · StreamSubmod.optVal f k, the finite maximum over |T| ≤ k; reason: notation
--   - encoding: a cardinality k → the hypothesis 1 ≤ k; reason: only k = 0 is excluded, where τ = (1/k) max_e f({e}) is undefined
-- source:
--   Udwani, Submodular Order Functions and Assortment Optimization, arXiv:2107.02743v5, Theorem 2, p.5 (proof §4.1, pp.20–21); Algorithms 1–2, p.13

import Mathlib
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_SubmodOrder_IsWeakSubmodularOrder
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_SubmodOrder_OracleProg
import Definitions.Def_SubmodOrder_algorithm1

namespace SubmodOrder

/-- Theorem 2 (Udwani, *Submodular Order Functions and Assortment Optimization*,
arXiv:2107.02743v5, p.5; proof §4.1, pp.20–21): "For cardinality constrained maximization of a
monotone subadditive function f with a (known) weak submodular order, Algorithm 1 is (1−ε)0.5
approximate with O(n/ε log k) oracle queries, for any choice of ε ∈ (0,1)."

There is an absolute constant `C` such that for every finite ground set `α` of `n` elements,
every order `π : α ≃ Fin n`, every `k ≥ 1`, every `ε ∈ (0,1)` and every `f : Finset α → ℝ`:

1. if `f` is monotone and subadditive, `f(∅) = 0` and `π` is a weak submodular order of `f`,
   then the output `S` of Algorithm 1 run against the value oracle of `f` satisfies `|S| ≤ k` and
   `f(S) ≥ (1 − ε) · ½ · OPT`, `OPT = max {f(T) : |T| ≤ k}`;
2. Algorithm 1 makes at most `C · n · (1 + log k)/ε` oracle queries.

**Formalization Note.** Algorithm 1 is the oracle program `algorithm1 π k ε`, built from `π`,
`k` and `ε` only; it learns `f` only through queries, and `OracleProg.queries` counts them. Its
loop runs over `i = 1, …, max(1, ⌈log_{1+ε} k⌉)`: at `k = 1` the printed loop is empty. The
`O(n/ε log k)` bound is read as `C · n · (1 + log k)/ε` (natural logarithm) with `C` chosen
before every other quantity: the printed `n/ε · log k` vanishes at `k = 1`, where the singleton
queries for `τ` are still needed. The query bound is stated for every `f`. -/
theorem theorem_2_threshold_half_approx :
    ∃ C : ℝ, ∀ {α : Type} [Fintype α] [DecidableEq α] (n : ℕ) (π : α ≃ Fin n) (k : ℕ) (ε : ℝ)
      (f : Finset α → ℝ), 1 ≤ k → 0 < ε → ε < 1 →
      ((Monotone f ∧ Subadditive f ∧ f ∅ = 0 ∧ IsWeakSubmodularOrder f π) →
          (OracleProg.run f (algorithm1 π k ε)).card ≤ k ∧
            (1 - ε) * (1 / 2) * StreamSubmod.optVal f k ≤ f (OracleProg.run f (algorithm1 π k ε))) ∧
        (OracleProg.queries f (algorithm1 π k ε) : ℝ) ≤ C * n * (1 + Real.log k) / ε := by sorry

end SubmodOrder
