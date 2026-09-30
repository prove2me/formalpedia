-- Prove2me | Theorems.Thm_RevenueManagement_inefficient_never_optimal
-- name    : RevenueManagement.inefficient_never_optimal
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:32:52.173179+00:00
-- url     : https://prove2.me/theorems/8791a442-798c-46a1-bb4a-4b8cf88c3edb
-- title:
--   Proposition 2.3: an inefficient offer set is never an optimal solution of the choice-based Bellman equation (2.24)
-- statement:
--   In the choice-based model with a choice model, arrival probabilities in $[0, 1]$ and
--   nonnegative prices, in any period $1 \le t \le T$ with a positive arrival probability
--   $\lambda_t > 0$ and $x \ge 1$ units remaining, a set $S$ that is inefficient in the sense of
--   Definition 2.1 does not maximize $\lambda_t (R(S) - Q(S)\Delta V_{t+1}(x))$: some other
--   set does strictly better.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, p. 68, Proposition 2.3 (proof omitted in the book; the argument sketched after it uses ΔV_{t+1}(x) ≥ 0)

import Definitions.Def_RevenueManagement_singleResource

namespace RevenueManagement

theorem inefficient_never_optimal {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ)
    (p : Fin n → ℝ) (T : ℕ) (hP : IsChoiceModel P) (hlam : ∀ t, 0 ≤ lam t ∧ lam t ≤ 1)
    (hp : ∀ j, 0 ≤ p j) (t x : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) (hx : 1 ≤ x) (hpos : 0 < lam t)
    (S : Finset (Fin n)) (hS : IsInefficient P p S) :
    ¬ IsChoiceOptimal lam P p T t x S := by sorry

end RevenueManagement
