-- Prove2me | Theorems.Thm_SelectedSubset3SUM_Integer_Supplement_theorem_3_3
-- name    : SelectedSubset3SUM.Integer.Supplement.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:50:52.168197+00:00
-- url     : https://prove2.me/theorems/a3768eec-03a5-4066-a6d6-360724ed5451
-- title:
--   Theorem 3.3 — deterministic selected-entries convolution on $[r]^d$
-- statement:
--   There are one program for the scalar machine with exact division and constants $b,e\in\mathbb N$, $K>0$ such that the following holds for all naturals $n,r,d,t_1,t_2,s$ with $s\le t=t_1+t_2$ and every valid instance of Problem 3.1 over $[r]^d$ (real weights $f$ on $H_{r,d,t_1}$, $g$ on $H_{r,d,t_2}$, at most $n$ listed entries, queries $\mathcal C\subseteq H_{r,d,t}$). At every word width at least $b\,(d(\lfloor\lg r\rfloor+1)+\lfloor\lg\max(2,n)\rfloor+1)$, the program accepts with $(f\star_r g)(c)$ written for every $c\in\mathcal C$, and its total charge (input, outputs and executed instructions) is at most
--
--   $$K\,(1+dr)^e\,\Bigl(1+n+H_r(d,\le s)+|\mathcal C|\,H_r(d,t,\ge s)\Bigr).$$
--
--   That is, Problem 3.1 is solved in total deterministic time $(n+H_r(d,\le s)+|\mathcal C|H_r(d,t,\ge s))\,(dr)^{O(1)}$, uniformly over the base, the dimension, the two ranks and the cutoff. Larger cutoffs make preprocessing cost more and queries cost less.
--
--   This generalizes Theorem 2.2 from subsets to vectors with coordinates below $r$, and is the algorithm plugged into Theorem 3.4 to obtain Corollaries 3.5 and 3.6.
--
--   Differences from the source:
--   - encoding: (dr)^{O(1)} and n + H_r(d,≤s) + |C| H_r(d,t,≥s) → K (1+dr)^e (1 + n + H_r(d,≤s) + |C| H_r(d,t,≥s)), constants b,e,K before all parameters; reason: equivalent for d,r ≥ 1 (then H_r(d,≤s) ≥ 1 and 1+dr ≤ 2dr); the 1+ terms only keep the budget positive at d = 0 or on the empty cube r = 0 < d, where the page's product is 0
--   - encoding: f, g with O(n) nonzero entries, query set C → arbitrary-order duplicate-free lists of (vector, weight) pairs of total length at most n, and a duplicate-free query list; reason: every finite sparse instance has such a presentation; zero weights may be listed; the O(n) constant is absorbed in K
--   - reading: deterministic time on the real RAM → the mission's exact scalar machine (ring operations) plus exact division of a scalar by a word, with input presentation and outputs charged and word width b(d(⌊lg r⌋+1)+⌊lg max(2,n)⌋+1); reason: the page's proof divides by ∏ c_j!; footnote 7 assumes words wide enough to index the tables; no scalar test or conversion is available
-- source:
--   Timothy M. Chan, Reina Itakura, Zhiyuan Ma, Yuancheng Yu, STOC 2027 submission #1421 (October 2026), Theorem 3.3, p.12 (proof p.12, via Lemma 3.2, p.12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1421.pdf

import Definitions.Def_SelectedSubset3SUM_Integer_Supplement_Vector

namespace SelectedSubset3SUM.Integer.Supplement

/-- Theorem 3.3, p.12: for every cutoff `s ≤ t = t₁ + t₂`, Problem 3.1 over `[r]^d` (every base
`r`, every dimension `d`, every rank split, arbitrary real weights, every query) is solved
deterministically in `(n + H_r(d, ≤ s) + |𝒞| H_r(d, t, ≥ s)) (dr)^{O(1)}` total time.
`(1 + dr)^e` stands for `(dr)^{O(1)}` and `1 + (…)` for `(…)`, so that the bound is not `0`
at `d = 0` or on the empty cube `r = 0 < d`; for `r ≥ 1` both are equivalent to the page's form.
One program and constants `b, e, K` precede every instance parameter. -/
theorem theorem_3_3 :
    ∃ (code : List VecInstr) (b e : ℕ) (K : ℝ), 0 < b ∧ 0 < K ∧
      ∀ (n r d t₁ t₂ s : ℕ) (I : VecData ℝ r d), I.Valid n t₁ t₂ → s ≤ t₁ + t₂ →
        ∀ W ≥ vecWidth b n r d,
          ∃ fuel, VecRun code W n t₁ t₂ s fuel I ∧
            (vecCharge n t₁ t₂ s fuel I : ℝ) ≤
              K * (1 + (d : ℝ) * r) ^ e * (1 + vecCost r d (t₁ + t₂) s n I.queries.length) := by sorry

end SelectedSubset3SUM.Integer.Supplement
