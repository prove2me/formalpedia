-- Prove2me | Theorems.Thm_SubstitutePricing_Mixed_eq_36_15
-- name    : SubstitutePricing.Mixed.eq_36_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:01.789309+00:00
-- url     : https://prove2.me/theorems/652edf2e-829e-40a1-8712-414a71ec705e
-- title:
--   (36)–(37) — the margin equation (15) is equivalent to (36), which has exactly one root
-- statement:
--   This statement has two parts.
--
--   1. In the mixed pricing model, for every number of remaining periods $t$, inventory $x$ and real $m$, the left side of (15),
--   $$
--   \sum_{j \in S_2^+(x)} \Big(\frac{m - v_j}{\mu} - 1\Big) e^{(m + u_j)/\mu}, \qquad S_2^+(x) = S_2(x) \cup \{0\},\ v_0 = 0,\ v_j = r^j - \Delta^j\pi_{t-1}(x),\ u_j = a_j - r^j,
--   $$
--   equals the left side of (36),
--   $$
--   \Big((1 + \Theta)\Big(\frac{m}{\mu} - 1\Big) - \frac{1}{\mu}\sum_{j \in S_2(x)} \theta_j v_j\Big) e^{(m + u_0)/\mu}.
--   $$
--   2. For $\mu > 0$, any $\Theta \ge 0$, any reals $C$, $u$ and any $\sigma \ge 0$, the equation
--   $$
--   \Big((1 + \Theta)\Big(\frac{m}{\mu} - 1\Big) - \frac{C}{\mu}\Big) e^{(m + u)/\mu} = \sigma
--   $$
--   has exactly one real solution $m$.
--
--   Together they show that the margin equation (15) of Proposition 2 has a unique solution $m_t(x)$, also when its right side vanishes ($S_1(x) = \emptyset$).
--
--   **Formalization Note** The printed (36) has $\Delta^j\pi_t(x_t)$ inside the sum; this is a misprint for $\Delta^j\pi_{t-1}(x_t)$, as (32) and (37) show, and the statement uses $\Delta^j\pi_{t-1}$. The case $\sigma = 0$ is included because Proposition 2 allows $S_1(x)$ to be empty.
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), pp. 337–338, App. A, proof of Proposition 2, (36)–(37)

import Definitions.Def_SubstitutePricing_Mixed_Model

namespace SubstitutePricing.Mixed
/-- (36)–(37): the left side of (15) equals the left side of (36), and (36) has exactly one
root for every nonnegative right side. -/
theorem eq_36_15 (M : Model) (hM : M.Assumptions) (t : ℕ) (x : Fin M.n → ℕ) :
    (∀ m : ℝ, M.lhs15 t x m =
      ((1 + M.Θ x) * (m / M.μ - 1) - (∑ j ∈ M.S2 x, M.θ j * M.v t j x) / M.μ) *
        Real.exp ((m + M.u0) / M.μ)) ∧
    (∀ Θ C u σ : ℝ, 0 ≤ Θ → 0 ≤ σ →
      ∃! m : ℝ, ((1 + Θ) * (m / M.μ - 1) - C / M.μ) * Real.exp ((m + u) / M.μ) = σ) := by sorry
end SubstitutePricing.Mixed
