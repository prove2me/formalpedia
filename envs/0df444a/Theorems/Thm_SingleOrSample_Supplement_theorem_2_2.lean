-- Prove2me | Theorems.Thm_SingleOrSample_Supplement_theorem_2_2
-- name    : SingleOrSample.Supplement.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:34:32.530817+00:00
-- url     : https://prove2.me/theorems/90c82202-9886-402f-84b8-9d0e55dd51c6
-- title:
--   Theorem 2.2 — no randomized algorithm is $(c,\beta)$-competitive with $\beta\ge1-c/3$, even for binary XOS valuations
-- statement:
--   For every $c\in(0,1]$, no randomized online allocation algorithm is $(c,\beta)$-competitive with $\beta\ge 1-c/3$ against an oblivious adversary, even when all valuations are binary XOS. Formally: there are $n$ and $m$ such that for every randomized online algorithm on $n$ agents and $m$ goods there are binary XOS valuations $v_1,\dots,v_n$ with
--   $$
--   \Pr\bigl[v_i(A_i)\ge c\cdot\mathrm{MMS}_i\ \text{for all } i\bigr]\ <\ 1-\frac{c}{3}.
--   $$
--
--   For XOS agents the failure probability of $c$-MMS is thus $\Omega(c)$, larger than the $\Omega(c^2)$ of the additive case (Theorem 2.1).
--
--   Differences from the source:
--   - encoding: no randomized algorithm can achieve (c, β)-competitiveness → there are n, m such that every algorithm on n agents and m goods has an instance in the class with success probability < β₀; reason: an algorithm for all sizes restricts to each size, and algorithms for different sizes are chosen independently, so the two forms are equivalent
--   - encoding: no randomized algorithm (an algorithm that tosses coins, any internal randomness) → every behavioural OnlineAlg: a law on the bundle at each arrival given the revealed valuations and earlier bundles; the named bundle is intersected with the available goods; reason: Kuhn's theorem (perfect recall) makes behavioural and general randomized algorithms induce the same laws; an algorithm that names only available goods is unchanged
--   - encoding: an allocation (A_1, …, A_n) ∈ Π_n([m]) → bundles that need not exhaust the goods; reason: valuations are monotone, so unallocated goods can go to anyone without lowering any v_i(A_i)
--   - encoding: agents 1, …, n → Fin n, from 0; reason: Lean convention; same instances
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Theorem 2.2, p.7 (pdf p.9)

import Mathlib
import Definitions.Def_SingleOrSample_Supplement_OnlineAlg
import Definitions.Def_SingleOrSample_Supplement_IsBinaryXOS

namespace SingleOrSample.Supplement

/-- **Theorem 2.2** (Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial
Agents, STOC 2027 submission, arXiv:2609.32286, manuscript sha256 28cd3d7b…, Theorem 2.2, p.7). For every `c ∈ (0, 1]` there are `n`, `m` such that
for every randomized online allocation algorithm there are binary XOS valuations `v_1, …, v_n` on
which the algorithm produces a `c`-MMS allocation with probability strictly less than `1 − c/3`: no
randomized algorithm is `(c, β)`-competitive with `β ≥ 1 − c/3`.

**Formalization Note.** As in Theorem 2.1: oblivious adversary, one size suffices. -/
theorem theorem_2_2 (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∃ n m : ℕ, ∀ A : OnlineAlg m, ∃ vs : Fin n → Finset (Fin m) → ℝ,
      (∀ i, IsBinaryXOS (vs i)) ∧
      (A.runLaw vs n).toOuterMeasure {bs | IsAlphaMMS c vs bs} < ENNReal.ofReal (1 - c / 3) := by sorry

end SingleOrSample.Supplement
