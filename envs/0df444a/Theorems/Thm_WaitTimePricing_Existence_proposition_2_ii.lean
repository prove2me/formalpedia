-- Prove2me | Theorems.Thm_WaitTimePricing_Existence_proposition_2_ii
-- name    : WaitTimePricing.Existence.proposition_2_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T11:25:47.997765+00:00
-- url     : https://prove2.me/theorems/35e63527-9ca2-4ae9-83bb-0fd96be8d0b6
-- title:
--   Proposition 2(ii) — the joining price bound $\Gamma(w)\le U'(0)$ and (8)
-- statement:
--   For every $w\in[0,\bar w]$ the joining price bound satisfies $0\le\Gamma(w)\le U'(0)$, and for every price $p\in[0,U'(0)]$,
--   $$U(\mathtt t(p))-p\,\mathtt t(p)-c(w)\ge 0\iff p\in[0,\Gamma(w)].$$
--   Equivalently, $\mathtt t(p,w)=\mathtt t(p)$ for $p\in[0,\Gamma(w)]$ and $\mathtt t(p,w)=0$ for $\Gamma(w)<p\le U'(0)$.
--
--   $\Gamma(w)$ is the highest price at which a customer facing wait time $w$ still joins; it is the upper limit of the price range in the optimality equations (12)–(13).
--
--   **Formalization Note** $\mathtt t(p)$ is defined only for $p\in[0,U'(0)]$ (5), so every statement about prices ranges there. $\Gamma(w)$ is defined as the supremum of the joining prices in $[0,U'(0)]$, not by a closed form.
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 9, Proposition 2(ii), (8)

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting

namespace WaitTimePricing.Existence

open Set Filter

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 9, Proposition 2(ii), (8).

For any `w ∈ [0, w̄]` there is an upper bound `Γ(w) ≤ U′(0)` such that `t(p, w) = 0` for
`p > Γ(w)` and `t(p, w) = t(p)` otherwise, or equivalently `U(t(p)) − p·t(p) − c(w) ≥ 0` if and
only if `p ∈ [0, Γ(w)]`.

**Formalization Note.** `t(p)` is defined for `p ∈ [0, U′(0)]` only (5), so every quantifier over
`p` ranges there. `Gamma M w` is defined as the supremum of the joining prices in `[0, U′(0)]`,
not by a closed form; the theorem asserts `0 ≤ Γ(w) ≤ U′(0)`, the equivalence (8), and the two
values of `t(p, w)`. -/
theorem proposition_2_ii (M : Model) (hM : M.Standing) :
    ∀ w ∈ Icc 0 (wbar M),
      0 ≤ Gamma M w ∧ Gamma M w ≤ deriv M.U 0 ∧
      (∀ p ∈ Icc 0 (deriv M.U 0),
        (0 ≤ M.U (tOf M p) - p * tOf M p - M.c w ↔ p ≤ Gamma M w)) ∧
      (∀ p ∈ Icc 0 (deriv M.U 0), Gamma M w < p → tJoin M p w = 0) ∧
      (∀ p ∈ Icc 0 (Gamma M w), tJoin M p w = tOf M p) := by sorry

end WaitTimePricing.Existence
