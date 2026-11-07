-- Prove2me | Theorems.Thm_TIEMaximin_eq_19
-- name    : TIEMaximin.eq_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:43:59.220011+00:00
-- url     : https://prove2.me/theorems/27727c48-80a4-4d25-b72e-468cf361b784
-- title:
--   Equation (19) — the counting bound $d_i+2k_i-1\le6a_i$
-- statement:
--   Let $m\ge n\ge2$, $\alpha=1/6$, and let $v$ be a nonnegative profile. Every deficient agent $i$ satisfies
--
--   $$d_i+2k_i-1\le6a_i.$$
--
--   This is inequality (18) at $\alpha=1/6$: it is what makes the compensated value reach $\mathrm{TPS}_i/6$, and it is where the constant of Theorem 1.1 comes from.
--
--   Differences from the source:
--   - encoding: agents N, goods M, nonnegative additive valuations → `Fin n`, `Fin m` (0-based), real matrices with the hypothesis `Nonneg`, bundle value `valOf`; reason: Lean convention; same instances
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), §5.2, eq. (19), p.24

import Mathlib
import Definitions.Def_TIEMaximin_Basic
import Definitions.Def_TIEMaximin_Comparison

namespace TIEMaximin

/-- **Equation (19)** (§5.2, p.24). Every deficient agent `i` satisfies `d_i + 2k_i − 1 ≤ 6a_i`, which
is (18) for `α = 1/6`.

arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, §5.2, eq. (19), p.24.

**Formalization Note.** `α = 1/6`; both cases of p.24 are covered, so there is no case hypothesis. -/
theorem eq_19 {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) (v : Fin n → Fin m → ℝ) (hv : Nonneg v)
    (i : Fin n) (hi : IsDeficient (1 / 6) v i) :
    dCost (1 / 6) v i + 2 * (kDef (1 / 6) v i : ℤ) - 1 ≤ 6 * aDef (1 / 6) v i := by sorry

end TIEMaximin
