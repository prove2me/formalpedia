-- Prove2me | Theorems.Thm_SingleOrSample_Supplement_theorem_C_6
-- name    : SingleOrSample.Supplement.theorem_C_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:37:29.322211+00:00
-- url     : https://prove2.me/theorems/fde9a8aa-b08f-4c01-8610-024da675ca4b
-- title:
--   Theorem C.6 — on the random-pool distribution every deterministic online algorithm succeeds with probability $\le d\,e^{-\alpha K/(2(d+1))}+d^3/(\alpha^2n)$
-- statement:
--   Let $\alpha\in(0,1]$ and let $K\ge1$ be an integer. Put $d=\lceil1/\alpha\rceil$, $n=(d+1)K^{2^d-1}$ agents and $m=n^{d+3}$ goods, and let $\mathcal D_{n,\alpha}$ be the random-pool instance distribution of Appendix C.2.
--
--   1. For every deterministic online allocation algorithm $A$,
--   $$
--   \Pr_{I\sim\mathcal D_{n,\alpha}}\bigl[A\text{ produces an }\alpha\text{-MMS allocation}\bigr]\ \le\ \eta_{n,\alpha}:=d\exp\Bigl(-\frac{\alpha K}{2(d+1)}\Bigr)+\frac{d^3}{\alpha^2 n}.
--   $$
--   2. In particular, with $\alpha=2/\log_2\log_2 n$, $\eta_{n,\alpha}=o(1)$: for every $\varepsilon>0$ there is $N$ such that $\eta_{n,\alpha}\le\varepsilon$ for every $n\ge N$ of the form $n=(d+1)K^{2^d-1}$ with $d=\lceil1/\alpha\rceil$, $\alpha\in(0,1]$ and $K\ge1$ an integer.
--
--   By Yao's principle this bound for deterministic algorithms on one input distribution yields Theorem 6.1 for randomized algorithms.
--
--   **Formalization Note** The success probability is taken under the joint law of the instance and the (deterministic) run. In clause 2, $K$ is determined by $n$ and $d$.
--
--   Differences from the source:
--   - generalization: n a sufficiently large integer of the form (d+1)K^(2^d−1) (App. C.2, p.35) → clause 1 holds for every α ∈ (0, 1] and every integer K ≥ 1; reason: largeness of n is used only for the o(1) clause (K ≥ 2α² log n); Lemmas C.2–C.5 and the union bound need only d ≥ 1, q_{r+1} ≤ n q_r and M_r ≥ n²; the large-n case is a special case
--   - reading: agents arrive with consecutive pool groups in the support order specified above → rounds in order; within a round pools in the order of their bins' positions, i.e. (parent pool, label) lexicographically; reason: the page specifies no other order; the analysis does not depend on the order of the pools within a round
--   - reading: α = 2/log log n (base unstated) → α = 2/log₂ log₂ n; reason: as in Theorem 6.1, whose proof this clause serves
--   - encoding: η_{n,α} = o(1) → for every ε > 0 there is N with η ≤ ε for every admissible n ≥ N (n = (d+1)K^(2^d−1), d = ⌈1/α⌉, 0 < α ≤ 1); reason: the limit is along the n for which D_{n,α} is defined; α ∈ (0, 1] holds for every n ≥ 16
--   - encoding: Pr_{I∼D_{n,α}}[A produces an α-MMS allocation] → successProb A.toAlg α (randomPool n m d K): the joint law of the instance and the point-mass run; reason: for a deterministic algorithm the run given the instance is a point mass
--   - encoding: an allocation (A_1, …, A_n) ∈ Π_n([m]) → bundles that need not exhaust the goods; reason: valuations are monotone, so unallocated goods can go to anyone without lowering any v_i(A_i)
--   - encoding: agents 1, …, n → Fin n, from 0; reason: Lean convention; same instances
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Theorem C.6, p.39 (pdf p.41); construction App. C.2, pp.35–36 (pdf pp.37–38)

import Mathlib
import Definitions.Def_SingleOrSample_Supplement_OnlineAlg
import Definitions.Def_SingleOrSample_Supplement_randomPool

namespace SingleOrSample.Supplement

/-- **Theorem C.6** (Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial
Agents, STOC 2027 submission, arXiv:2609.32286, manuscript sha256 28cd3d7b…, Theorem C.6, p.39, with the construction of App. C.2, pp.35–36).
1. For every `α ∈ (0, 1]` and integer `K ≥ 1`, with `d = ⌈1/α⌉`, `n = (d+1)K^(2^d − 1)` agents and
   `m = n^(d+3)` goods, every deterministic online allocation algorithm produces an `α`-MMS allocation
   on an instance drawn from the random-pool distribution `D_{n,α}` with probability at most
   `η_{n,α} = d·exp(−αK/(2(d+1))) + d³/(α²n)`.
2. With `α = 2/log₂ log₂ n`, `η_{n,α} = o(1)`: for every `ε > 0` there is `N` such that
   `η_{n,α} ≤ ε` for every `n ≥ N` of the form `(d+1)K^(2^d − 1)` with `d = ⌈1/α⌉` and `α ∈ (0, 1]`.

**Formalization Note.** App. C.2 takes `n` "sufficiently large"; that is used only for the
`o(1)` clause (`K ≥ 2α² log n`), so clause 1 is stated for every `α ∈ (0,1]` and `K ≥ 1`. `K` is
determined by `n` and `d` in clause 2. The logarithms are base `2`. -/
theorem theorem_C_6 :
    (∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (K d n m : ℕ), 1 ≤ K → d = ⌈1 / α⌉₊ →
      n = (d + 1) * K ^ (2 ^ d - 1) → m = n ^ (d + 3) →
      ∀ A : DetOnlineAlg m,
        successProb A.toAlg α (randomPool n m d K) ≤
          ENNReal.ofReal ((d : ℝ) * Real.exp (-(α * K) / (2 * ((d : ℝ) + 1))) +
            (d : ℝ) ^ 3 / (α ^ 2 * n))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ (n K d : ℕ) (α : ℝ), N ≤ n → 1 ≤ K →
      α = 2 / Real.logb 2 (Real.logb 2 n) → 0 < α → α ≤ 1 → d = ⌈1 / α⌉₊ →
      n = (d + 1) * K ^ (2 ^ d - 1) →
      (d : ℝ) * Real.exp (-(α * K) / (2 * ((d : ℝ) + 1))) + (d : ℝ) ^ 3 / (α ^ 2 * n) ≤ ε) := by sorry

end SingleOrSample.Supplement
