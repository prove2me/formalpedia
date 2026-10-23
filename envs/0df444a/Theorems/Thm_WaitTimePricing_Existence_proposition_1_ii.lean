-- Prove2me | Theorems.Thm_WaitTimePricing_Existence_proposition_1_ii
-- name    : WaitTimePricing.Existence.proposition_1_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T11:25:47.792983+00:00
-- url     : https://prove2.me/theorems/fae4f9ff-ee54-483f-b28e-3de3dfb300c4
-- title:
--   Proposition 1(ii) — the lower bound $L(w)$: $U(t)-U'(t)t-c(w)\ge0 \iff t\in[L(w),C]$
-- statement:
--   For every $w\in[0,\hat w]$ there is a unique $L(w)\in[0,C]$ such that, for all $t\in[0,C]$,
--   $$U(t)-U'(t)\,t-c(w)\ge 0\iff t\in[L(w),C].$$
--
--   $L(w)$ is the shortest service time a customer facing wait time $w$ accepts at the marginal price $U'(t)$.
--
--   **Formalization Note** The printed condition "if and only if $w\le\hat w$ and $t\in[L(w),C]$" has a redundant first conjunct since $w\in[0,\hat w]$; it is dropped. $L(w)$ is defined as the infimum of $\{t\in[0,C]:U(t)-U'(t)t-c(w)\ge0\}$; the statement asserts that it lies in $[0,C]$, has the property, and is the only point of $[0,C]$ with it.
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 8, Proposition 1(ii), (4)

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting

namespace WaitTimePricing.Existence

open Set Filter

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 8, Proposition 1(ii), (4).

For any `w ∈ [0, ŵ]` there is a unique lower bound `L(w) ∈ [0, C]` such that, for `t ∈ [0, C]`,
`U(t) − U′(t)t − c(w) ≥ 0` if and only if `t ∈ [L(w), C]`.

**Formalization Note.** The printed clause "if and only if `w ≤ ŵ` and `t ∈ [L(w), C]`" has a
redundant first conjunct, since `w ∈ [0, ŵ]` is assumed; it is dropped. `Lw M w` is defined as the
infimum of `{t ∈ [0, C] | U(t) − U′(t)t − c(w) ≥ 0}`; the theorem asserts that it lies in `[0, C]`,
that it has property (4), and that it is the only point of `[0, C]` with that property. -/
theorem proposition_1_ii (M : Model) (hM : M.Standing) :
    ∀ w ∈ Icc 0 (what M),
      Lw M w ∈ Icc 0 M.C ∧
      (∀ t ∈ Icc 0 M.C, 0 ≤ M.U t - deriv M.U t * t - M.c w ↔ Lw M w ≤ t) ∧
      (∀ L ∈ Icc 0 M.C,
        (∀ t ∈ Icc 0 M.C, 0 ≤ M.U t - deriv M.U t * t - M.c w ↔ L ≤ t) → L = Lw M w) := by sorry

end WaitTimePricing.Existence
