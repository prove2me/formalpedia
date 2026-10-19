-- Prove2me | Theorems.Thm_PrivSeqLearn_QueryComplexity_special_cover_bound
-- name    : PrivSeqLearn.QueryComplexity.special_cover_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:30.982818+00:00
-- url     : https://prove2.me/theorems/3bedf1af-f72b-446f-b835-717c4f766387
-- title:
--   p. 21 — if 2ϵ < δ, the δ-cover number of Ī(q) is at most (K + 3)/2, K the number of special queries in [δ, 1]
-- statement:
--   Let $\epsilon > 0$ and $\delta > 2\epsilon$, and let $\bar q = (q_1, \dots, q_N)$ be a query vector with every $q_k \in [0,1)$. Let $\bar{\mathcal I}(\bar q)$ be the union of the special intervals of $\bar q$ and $K$ the number of special queries, the points of $[\delta, 1]$ that are endpoints of special intervals. Then
--   $$C_\delta\big(\bar{\mathcal I}(\bar q)\big) \le \frac{K + 3}{2}.$$
--
--   This is the covering half of the lower bound: a private strategy needs $C_\delta \ge L$, hence $K \ge 2L - 3$ special queries.
--
--   **Formalization Note** The bound is written $2\,C_\delta(\bar{\mathcal I}(\bar q)) \le K + 3$ in $\mathbb N$. No strategy enters; the range condition $q_k \in [0,1)$ is the codomain of the paper's query maps, and without it special intervals outside $[0,1]$ would not be counted in $K$.
-- source:
--   Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, p. 21, §7.2 (with the definition of special queries, p. 20)

import Mathlib
import Definitions.Def_PrivSeqLearn_QueryComplexity_Setting
import Definitions.Def_PrivSeqLearn_QueryComplexity_SpecialIntervals

namespace PrivSeqLearn.QueryComplexity

/-- The cover bound of §7.2 (Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, p. 21): if `2ϵ < δ`, the `δ`-cover number of the union `Ī(q)`
of special intervals is at most `(K + 3)/2`, where `K` is the number of special queries (endpoints
of special intervals lying in `[δ, 1]`).

**Formalization Note** Stated for every query vector `q` with values in `[0, 1)` (the range of the
paper's query maps); no strategy is involved. The bound `C ≤ (K+3)/2` is written `2C ≤ K + 3` in `ℕ`. -/
theorem special_cover_bound {N : ℕ} (ϵ δ : ℝ) (hϵ : 0 < ϵ) (h2ϵδ : 2 * ϵ < δ)
    (q : Fin N → ℝ) (hq : ∀ k, q k ∈ Set.Ico (0 : ℝ) 1) :
    2 * coverNumber δ (specialUnion ϵ q) ≤ (specialQueries ϵ δ q).ncard + 3 := by sorry

end PrivSeqLearn.QueryComplexity
