-- Prove2me | Theorems.Thm_QuerySampleRev_parameter_facts
-- name    : QuerySampleRev.parameter_facts
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T01:36:14.119198+00:00
-- url     : https://prove2.me/theorems/4d8e518a-7a3a-4ba8-9482-12567d8a0284
-- title:
--   §5.5 (proof of Theorem 21) — parameter facts: $\rho w=2\varepsilon$, bounds on $K$ and $\rho\le\frac14$, disjoint $P^{(i)}\subseteq[\frac54,\frac32]$
-- statement:
--   Let $c\in[0,1]$ and $0<\varepsilon\le1/128$, and set $K=\max\{2,\lfloor\varepsilon^{-c}/64\rfloor\}$, $w=1/(8K)$, $\rho=16K\varepsilon$, $a_i=3/2-2iw$, $b_i=a_i+2w$ and $P^{(i)}=(a_i,b_i]$. Then
--   1. $\rho w=2\varepsilon$;
--   2. $2^{-7}\varepsilon^{-c}\le K\le2\varepsilon^{-c}$;
--   3. $\rho\le\max\{32\varepsilon,\varepsilon^{1-c}/4\}\le1/4$;
--   4. the intervals $P^{(i)}$, $i\in[K]$, are pairwise disjoint;
--   5. each $P^{(i)}$, $i\in[K]$, lies in $[5/4,3/2]$.
--
--   These are the parameter facts the lower-bound construction of Theorem 21 relies on: $\rho\le1/4$ keeps the hard densities positive and quasi-MHR, and the bounds on $K$ convert the per-interval bound into the $\varepsilon^{-(2+c)}$ rate.
--
--   Differences from the source:
--   - encoding: $K=\max\{2,\lfloor\varepsilon^{-c}/64\rfloor\}$ and $i\in[K]$ → `max 2 ⌊ε ^ (-c) / 64⌋₊` with the real power, and $i\in$ `Finset.Icc 1 K`; reason: same values; $\varepsilon^{-c}/64>0$ so the natural floor is the floor
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), §5.5, proof of Theorem 21, p.36 (PDF p.38)

import Mathlib
import Definitions.Def_QuerySampleRev_priceInterval

namespace QuerySampleRev

/-- **Parameter facts of the construction.** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue
Maximization* (manuscript, sha256 c31ea3d3…), §5.5, proof of Theorem 21, p.36 (PDF 38): "These choices
satisfy `ρw = 2ε` and `2^{−7}ε^{−c} ≤ K ≤ 2ε^{−c}`. They also satisfy `ρ ≤ max{32ε, ε^{1−c}/4} ≤ 1/4`,
where the last inequality uses `ε ≤ 1/128` and `c ≤ 1`. … The intervals `P⁽ⁱ⁾` are pairwise disjoint
and lie in `[5/4, 3/2]`."

For `c ∈ [0, 1]` and `0 < ε ≤ 1/128`, with `K = max{2, ⌊ε^{−c}/64⌋}`, `w = 1/(8K)`, `ρ = 16Kε` and
`P⁽ⁱ⁾ = (3/2 − 2iw, 3/2 − 2iw + 2w]`. -/
theorem parameter_facts {c ε : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hε0 : 0 < ε) (hε : ε ≤ 1 / 128) :
    rho ε c * halfWidth ε c = 2 * ε ∧
    ε ^ (-c) / 2 ^ 7 ≤ (numHard ε c : ℝ) ∧ (numHard ε c : ℝ) ≤ 2 * ε ^ (-c) ∧
    rho ε c ≤ max (32 * ε) (ε ^ (1 - c) / 4) ∧ max (32 * ε) (ε ^ (1 - c) / 4) ≤ 1 / 4 ∧
    (∀ i ∈ Finset.Icc 1 (numHard ε c), ∀ j ∈ Finset.Icc 1 (numHard ε c), i ≠ j →
      Disjoint (priceInterval ε c i) (priceInterval ε c j)) ∧
    (∀ i ∈ Finset.Icc 1 (numHard ε c), priceInterval ε c i ⊆ Set.Icc (5 / 4) (3 / 2)) := by sorry

end QuerySampleRev
