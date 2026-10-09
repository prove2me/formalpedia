-- Prove2me | Theorems.Thm_RobustPoA_Repeated_relation_25
-- name    : RobustPoA.Repeated.relation_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:37:32.507983+00:00
-- url     : https://prove2.me/theorems/667a1dc8-3b09-4d56-a223-3113fff24c8a
-- title:
--   Relation (25), p. 14 — time-averaged smoothness bound
-- statement:
--   In a $(\lambda,\mu)$-smooth cost-minimization game with $\mu<1$, let $s^1,s^2,\ldots$ be any outcome sequence and let $s'$ be a comparison outcome. For every integer $T\geq1$,
--
--   $$\frac1T\sum_{t=1}^{T}C(s^t)\leq\frac{\lambda}{1-\mu}C(s')+\frac1{1-\mu}\sum_i\left(\frac1T\sum_{t=1}^{T}\delta_i(s^t;s')\right).$$
--
--   This is the average-cost inequality before any no-regret condition is imposed.
--
--   **Formalization Note** The comparison outcome is arbitrary; the paper's preceding setup calls it minimum-cost, but minimality is not used in this relation.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), (25), §3.2, p. 14

import Mathlib
import Definitions.Def_RobustPoA_Static_Smoothness
import Definitions.Def_RobustPoA_Repeated_Regret

namespace RobustPoA.Repeated

/-- Relation (25), the time average of relation (23). -/
theorem relation_25 {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (lam mu : ℝ)
    (hsm : RobustPoA.Static.IsSmooth C lam mu) (hmu : mu < 1)
    (seq : ℕ → ∀ i, S i) (s' : ∀ i, S i) (T : ℕ) (hT : 1 ≤ T) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, RobustPoA.Static.cost C (seq t) ≤
      lam / (1 - mu) * RobustPoA.Static.cost C s' +
        (1 / (1 - mu)) *
          ∑ i, ((1 / (T : ℝ)) *
            ∑ t ∈ Finset.Icc 1 T, delta C s' (seq t) i) := by sorry

end RobustPoA.Repeated
