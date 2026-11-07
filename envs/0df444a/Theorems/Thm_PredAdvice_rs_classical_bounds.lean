-- Prove2me | Theorems.Thm_PredAdvice_rs_classical_bounds
-- name    : PredAdvice.rs_classical_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:34:11.198344+00:00
-- url     : https://prove2.me/theorems/0cba4620-0241-40f1-bfe4-d19437753123
-- title:
--   Classical bounds $2^{\Omega(\log^* n)} \le RS(n) \le 2^{O(\sqrt{\log n})}$
-- statement:
--   There are absolute constants $c_1,c_2>0$ such that for every $n\ge 2$
--   $$
--   2^{c_1\log^* n}\ \le\ RS(n)\ \le\ 2^{c_2\sqrt{\log_2 n}} .
--   $$
--
--   This is the classical pair of bounds on the Ruzsa–Szemerédi function: the lower bound comes from the triangle removal lemma, the upper bound from Behrend-type constructions of many large induced matchings. The lower bound gives $RS(n)\to\infty$, which is what makes the execution space of Theorem 1.1 $o(n^2\log n)$.
--
--   Differences from the source:
--   - encoding: asymptotic bounds 2^{Ω(log* n)} ≤ RS(n) ≤ 2^{O(√log n)} → constants c₁, c₂ > 0 with the bounds for every n ≥ 2; reason: RS(n) > 0 for n ≥ 2, so finitely many small n are absorbed into the constants; RS(n) is undefined for n ≤ 1
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), §1.1, p.4 (citing [KUV19])

import Mathlib
import Definitions.Def_PredAdvice_RS
import Definitions.Def_PredAdvice_logStar

set_option autoImplicit false

namespace PredAdvice

/-- **Classical bounds on the Ruzsa–Szemerédi function** (Kopelowitz, Korin, Roditty, *Using Small Advice to Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), §1.1, p.4, citing [KUV19]):
`2^{Ω(log* n)} ≤ RS(n) ≤ 2^{O(√log n)}`.

**Formalization Note** The `Ω` and `O` are absolute constants `c₁, c₂ > 0`, and the bounds are
stated for every `n ≥ 2` (for `n ≤ 1` the function is undefined). Since `RS(n) > 0` for `n ≥ 2`
and finitely many small `n` can be absorbed into the constants, this is the same as the
asymptotic form. -/
theorem rs_classical_bounds :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ n : ℕ, 2 ≤ n →
      (2 : ℝ) ^ (c₁ * (logStar n : ℝ)) ≤ RS n ∧
        RS n ≤ (2 : ℝ) ^ (c₂ * Real.sqrt (Real.logb 2 n)) := by sorry

end PredAdvice
