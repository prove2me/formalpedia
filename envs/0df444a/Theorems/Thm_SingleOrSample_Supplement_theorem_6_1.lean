-- Prove2me | Theorems.Thm_SingleOrSample_Supplement_theorem_6_1
-- name    : SingleOrSample.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:36:47.054568+00:00
-- url     : https://prove2.me/theorems/560c02b3-80e5-43ab-914d-6d252f3898e9
-- title:
--   Theorem 6.1 — no randomized algorithm guarantees $2/\log\log n$-MMS with probability $\Theta(1)$, even for simple binary XOS valuations with no large items
-- statement:
--   No randomized online allocation algorithm can guarantee a $\frac{2}{\log\log n}$-MMS allocation with probability $\Theta(1)$ against an oblivious adversary, even for simple binary XOS valuations with no large items. Formally, with $\alpha_n=2/\log_2\log_2 n$: for every $\beta>0$ and every $N$ there are $n\ge N$ and $m$ with $\alpha_n\in(0,1]$ such that every randomized online algorithm on $n$ agents and $m$ goods has an instance $v_1,\dots,v_n$ where
--
--   1. every $v_i$ is simple binary XOS ($n$ pairwise disjoint bins of equal positive size);
--   2. there are no large items: $v_i(\{g\})\le n^{-2}\,\mathrm{MMS}_i$ for all $i$ and goods $g$;
--   3. the algorithm succeeds with small probability:
--   $$
--   \Pr\bigl[v_i(A_i)\ge\alpha_n\cdot\mathrm{MMS}_i\ \text{for all } i\bigr]\ <\ \beta.
--   $$
--
--   Together with the $O(1/\log n)$-MMS algorithm of Section 6, this separates XOS from submodular valuations, for which Theorem 4.1 gives constant MMS with constant probability.
--
--   **Formalization Note** The proof goes through Theorem C.6 and Yao's principle.
--
--   Differences from the source:
--   - reading: cannot guarantee … with probability Θ(1) → for every β > 0 and every N there is n ≥ N with an instance whose success probability is < β; reason: this is the negation of a constant β > 0 with success probability ≥ β for all large n
--   - reading: log log n (base unstated) → log₂ log₂ n; reason: for large n base 2 gives the smaller α_n, so the lower bound is the stronger one and implies the natural-log version
--   - reading: simple binary-XOS valuations (Table 1 note (∗): binary, O(n) clauses, MMS value and partition computable in O(m + n) time) → IsSimpleBinaryXOS n: n pairwise disjoint clauses of equal positive size; reason: the structural class is contained in the paper's simple class (n clauses, MMS value the bin size, MMS partition one bin per bundle) and is the form of every valuation of App. C.2; a smaller instance class makes the lower bound stronger; running time is not a mathematical predicate
--   - encoding: 2/log log n-MMS with α ∈ [0, 1] (Definition 2) → the conclusion also asserts 0 < α_n ≤ 1; reason: rules out meeting the existential at a small n where α_n is outside [0, 1]; automatic for n ≥ 16
--   - encoding: no randomized algorithm (an algorithm that tosses coins, any internal randomness) → every behavioural OnlineAlg: a law on the bundle at each arrival given the revealed valuations and earlier bundles; the named bundle is intersected with the available goods; reason: Kuhn's theorem (perfect recall) makes behavioural and general randomized algorithms induce the same laws; an algorithm that names only available goods is unchanged
--   - encoding: an allocation (A_1, …, A_n) ∈ Π_n([m]) → bundles that need not exhaust the goods; reason: valuations are monotone, so unallocated goods can go to anyone without lowering any v_i(A_i)
--   - encoding: agents 1, …, n → Fin n, from 0; reason: Lean convention; same instances
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Theorem 6.1, p.19 (pdf p.21), restated p.34 (pdf p.36)

import Mathlib
import Definitions.Def_SingleOrSample_Supplement_OnlineAlg
import Definitions.Def_SingleOrSample_Supplement_IsBinaryXOS

namespace SingleOrSample.Supplement

/-- **Theorem 6.1** (Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial
Agents, STOC 2027 submission, arXiv:2609.32286, manuscript sha256 28cd3d7b…, Theorem 6.1, p.19, restated p.34). No randomized online allocation
algorithm guarantees a `2/log log n`-MMS allocation with probability `Θ(1)`, even for simple
binary-XOS valuations with no large items: for every `β > 0` and every `N` there are `n ≥ N` and `m`
such that `α_n = 2/log₂ log₂ n` lies in `(0, 1]` and every randomized online algorithm has an instance
of simple binary-XOS valuations with `v_i({g}) ≤ n^{−2} MMS_i` for all `i`, `g` on which it produces an
`α_n`-MMS allocation with probability less than `β`.

**Formalization Note.** "Cannot guarantee with probability `Θ(1)`" is the negation of "there is a
constant `β > 0` with success probability at least `β` for all large `n`". The logarithms are base
`2`, which gives the smaller `α_n` for large `n` and so the stronger lower bound. The instance is
chosen after the algorithm and before its coins (oblivious adversary). -/
theorem theorem_6_1 (β : ℝ) (hβ : 0 < β) (N : ℕ) :
    ∃ n m : ℕ, N ≤ n ∧ 0 < 2 / Real.logb 2 (Real.logb 2 n) ∧
      2 / Real.logb 2 (Real.logb 2 n) ≤ 1 ∧
      ∀ A : OnlineAlg m, ∃ vs : Fin n → Finset (Fin m) → ℝ,
        (∀ i, IsSimpleBinaryXOS n (vs i)) ∧
        (∀ (i : Fin n) (g : Fin m),
          vs i {g} ≤ 1 / (n : ℝ) ^ 2 * LittleCharity.MMS.mms (vs i) n Finset.univ) ∧
        (A.runLaw vs n).toOuterMeasure
            {bs | IsAlphaMMS (2 / Real.logb 2 (Real.logb 2 n)) vs bs} < ENNReal.ofReal β := by sorry

end SingleOrSample.Supplement
