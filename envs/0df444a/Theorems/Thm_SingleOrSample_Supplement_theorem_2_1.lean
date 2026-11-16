-- Prove2me | Theorems.Thm_SingleOrSample_Supplement_theorem_2_1
-- name    : SingleOrSample.Supplement.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:33:57.97376+00:00
-- url     : https://prove2.me/theorems/58a3c815-235e-4a72-ad57-3bfa605d5cd3
-- title:
--   Theorem 2.1 — no randomized algorithm is $(c,\beta)$-competitive with $\beta\ge1-c^2/5$, even for binary additive valuations
-- statement:
--   For every $c\in(0,1]$, no randomized online allocation algorithm is $(c,\beta)$-competitive with $\beta\ge 1-c^2/5$ against an oblivious adversary, even when all valuations are binary additive. Formally: there are $n$ and $m$ such that for every randomized online algorithm on $n$ agents and $m$ goods there are binary additive valuations $v_1,\dots,v_n$ with
--   $$
--   \Pr\bigl[v_i(A_i)\ge c\cdot\mathrm{MMS}_i\ \text{for all } i\bigr]\ <\ 1-\frac{c^2}{5},
--   $$
--   where the probability is over the algorithm's coins and $\mathrm{MMS}_i$ is the maximin share of $v_i$ for $n$ bundles of all $m$ goods.
--
--   So achieving $c$-MMS online entails an $\Omega(c^2)$ failure probability, which sets the scale for the paper's upper bounds.
--
--   Differences from the source:
--   - encoding: no randomized algorithm can achieve (c, β)-competitiveness → there are n, m such that every algorithm on n agents and m goods has an instance in the class with success probability < β₀; reason: an algorithm for all sizes restricts to each size, and algorithms for different sizes are chosen independently, so the two forms are equivalent
--   - encoding: no randomized algorithm (an algorithm that tosses coins, any internal randomness) → every behavioural OnlineAlg: a law on the bundle at each arrival given the revealed valuations and earlier bundles; the named bundle is intersected with the available goods; reason: Kuhn's theorem (perfect recall) makes behavioural and general randomized algorithms induce the same laws; an algorithm that names only available goods is unchanged
--   - encoding: an allocation (A_1, …, A_n) ∈ Π_n([m]) → bundles that need not exhaust the goods; reason: valuations are monotone, so unallocated goods can go to anyone without lowering any v_i(A_i)
--   - encoding: agents 1, …, n → Fin n, from 0; reason: Lean convention; same instances
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Theorem 2.1, p.7 (pdf p.9)

import Mathlib
import Definitions.Def_SingleOrSample_Supplement_OnlineAlg
import Definitions.Def_SingleOrSample_Supplement_IsBinaryXOS

namespace SingleOrSample.Supplement

/-- **Theorem 2.1** (Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial
Agents, STOC 2027 submission, arXiv:2609.32286, manuscript sha256 28cd3d7b…, Theorem 2.1, p.7). For every `c ∈ (0, 1]` there are `n`, `m` such that
for every randomized online allocation algorithm there are binary additive valuations
`v_1, …, v_n` on which the algorithm produces a `c`-MMS allocation with probability strictly less
than `1 − c²/5`: no randomized algorithm is `(c, β)`-competitive with `β ≥ 1 − c²/5`.

**Formalization Note.** The instance is chosen after the algorithm and before its coins (oblivious
adversary). An algorithm defined for all sizes is `(c, β)`-competitive only if it is so at every `n`,
`m`, so exhibiting one size is the page's claim. Bundles need not exhaust the goods. -/
theorem theorem_2_1 (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∃ n m : ℕ, ∀ A : OnlineAlg m, ∃ vs : Fin n → Finset (Fin m) → ℝ,
      (∀ i, IsBinaryAdditive (vs i)) ∧
      (A.runLaw vs n).toOuterMeasure {bs | IsAlphaMMS c vs bs} < ENNReal.ofReal (1 - c ^ 2 / 5) := by sorry

end SingleOrSample.Supplement
