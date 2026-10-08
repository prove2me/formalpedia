-- Prove2me | Theorems.Thm_SubstitutePricing_Dynamic_theorem_1
-- name    : SubstitutePricing.Dynamic.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:03.824979+00:00
-- url     : https://prove2.me/theorems/33a90230-a351-40bb-8b21-71016228b895
-- title:
--   Theorem 1 — optimal dynamic prices equalize marginal revenues
-- statement:
--   Under the substitute-product MNL model, with $t\geq1$ periods remaining and any nonnegative integer inventory $x$, the margin equation has a unique real solution $m_t(x)$:
--
--   $$
--   \left(\frac{m_t(x)}{\mu}-1\right)\exp\left(\frac{m_t(x)+u_0}{\mu}\right)=\sum_{i\in S(x)}\exp\left(\frac{a_i-\Delta^i\pi_{t-1}(x)}{\mu}\right).
--   $$
--
--   For every solution of this equation, the prices $r_i^*=\Delta^i\pi_{t-1}(x)+m_t(x)$ on $S(x)$ are nonnegative, attain the Bellman maximum, and satisfy $m_t(x)P_0(x,r^*)=\mu$. At the same inventory $x$, let $m_s(x)$ solve the corresponding equation for every $s=1,\ldots,t$. Then
--
--   $$
--   \pi_t(x)=\lambda\sum_{s=1}^{t}\bigl[m_s(x)-\mu\bigr].
--   $$
--
--   The theorem gives both an optimal pricing rule and the maximum expected revenue for every inventory state, including the empty state.
--
--   **Formalization Note** The real supremum in the Bellman definition is paired with explicit maximizer attainment and equality to the objective. Out-of-stock prices are represented by removal from the choice set; their stored candidate coordinates are zero. The root is asserted unique rather than selected invisibly.
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), p. 323, Theorem 1, (9)–(11)

import Definitions.Def_SubstitutePricing_Dynamic_Model

namespace SubstitutePricing.Dynamic
/-- Theorem 1: equal marginal revenues, the margin equation, and total expected revenue. -/
theorem theorem_1 (M : Model) (hM : M.Assumptions) (t : ℕ) (ht : 1 ≤ t)
    (x : Fin M.n → ℕ) :
    (∃! m : ℝ, M.marginLHS m = M.sigma t x) ∧
    (∀ m : ℝ, M.marginLHS m = M.sigma t x →
      M.rstar t x m ∈ M.feasible ∧
      IsMaxOn (M.obj (M.pi (t - 1)) x) M.feasible (M.rstar t x m) ∧
      M.pi t x = M.obj (M.pi (t - 1)) x (M.rstar t x m) ∧
      m * M.P0 x (M.rstar t x m) = M.μ) ∧
    (∀ ms : ℕ → ℝ,
      (∀ s ∈ Finset.Icc 1 t, M.marginLHS (ms s) = M.sigma s x) →
      M.pi t x = M.lam * ∑ s ∈ Finset.Icc 1 t, (ms s - M.μ)) := by sorry
end SubstitutePricing.Dynamic
