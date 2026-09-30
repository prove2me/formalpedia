-- Prove2me | Theorems.Thm_RevenueManagement_choice_marginal_values
-- name    : RevenueManagement.choice_marginal_values
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:32:23.929951+00:00
-- url     : https://prove2.me/theorems/79dc0a13-62da-45ef-9701-3456bd3edaa2
-- title:
--   Proposition 2-2.A.4: in the choice-based model the marginal values ΔVₜ(x) are decreasing in the remaining capacity x and decreasing in time t
-- statement:
--   For the choice-based single-resource model (2.24)/(2.26) with a choice model, arrival
--   probabilities $\lambda_t \in [0, 1]$ and nonnegative prices, for every period
--   $1 \le t \le T$ and $x \ge 1$: $\Delta V_t(x+1) \le \Delta V_t(x)$ and
--   $\Delta V_{t+1}(x) \le \Delta V_t(x)$.
--
--   **Formalization Note** The appendix prints the second inequality as
--   $\Delta V_t(x) \ge \Delta V_{t-1}(x)$, marginal values increasing with $t$. That direction
--   contradicts Proposition 2.2(ii) for the dynamic model, the claim of Theorem 2.3 that the
--   optimal index increases with $t$ (which needs $\Delta V_{t+1}(x)$ to decrease with $t$),
--   and numerical solution of (2.26); the statement here is the direction that holds, marginal
--   values decreasing with time.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, Appendix 2.A p. 79, Proposition 2-2.A.4, and p. 69 ('the marginal value ΔV_{t+1}(x) is decreasing in x (see Appendix 2.A for a proof)')

import Definitions.Def_RevenueManagement_singleResource

namespace RevenueManagement

theorem choice_marginal_values {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ)
    (p : Fin n → ℝ) (T : ℕ) (hP : IsChoiceModel P) (hlam : ∀ t, 0 ≤ lam t ∧ lam t ≤ 1)
    (hp : ∀ j, 0 ≤ p j) (t x : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) (hx : 1 ≤ x) :
    choiceDelta lam P p T t (x + 1) ≤ choiceDelta lam P p T t x ∧
      choiceDelta lam P p T (t + 1) x ≤ choiceDelta lam P p T t x := by sorry

end RevenueManagement
