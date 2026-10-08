-- Prove2me | Theorems.Thm_SubstitutePricing_Unified_proposition_1
-- name    : SubstitutePricing.Unified.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:19:42.387524+00:00
-- url     : https://prove2.me/theorems/1369831d-491e-4310-8e18-f801cf6f37a5
-- title:
--   Proposition 1 — the optimal unified dynamic price is Δʷπₜ₋₁(x) + mₜ(x), and πₜ(x) = λΣₛ[mₛ(x) − μ]
-- statement:
--   Consider the MNL substitute-product pricing model with quality indices $a_i$, no-purchase utility $u_0$, scale $\mu>0$ and arrival probability $\lambda\in(0,1]$, under **unified dynamic pricing**: in every period one common price $r\ge0$ is charged for all in-stock variates. Let $\pi_t$ be its value function ($\pi_0=0$, $t$ = remaining periods), $\Delta^i\pi_{t-1}(x)=\pi_{t-1}(x)-\pi_{t-1}(x-e^i)$, and
--   $$
--   \Delta^w\pi_{t-1}(x)=\frac{\sum_{i\in S(x)}e^{a_i/\mu}\Delta^i\pi_{t-1}(x)}{\sum_{i\in S(x)}e^{a_i/\mu}},\qquad a_w=\mu\ln\sum_{i\in S(x)}e^{a_i/\mu}.
--   $$
--   Let $t\ge1$ and let $x$ be an inventory level with $S(x)\neq\emptyset$. Then:
--   1. the equation
--   $$
--   \Bigl(\frac{m}{\mu}-1\Bigr)\exp\Bigl(\frac{m+u_0}{\mu}\Bigr)=\exp\Bigl(\frac{a_w-\Delta^w\pi_{t-1}(x)}{\mu}\Bigr)
--   $$
--   has a unique solution $m=m_t(x)$;
--   2. the price $r^*_t(x)=\Delta^w\pi_{t-1}(x)+m_t(x)$ (13) is nonnegative, attains the maximum in the optimality equation, $\pi_t(x)$ equals the objective at $r^*_t(x)$, and $m_t(x)P^0(r^*_t)=\mu$;
--   3. if $m_s(x)$ denotes the solution of the equation above for period $s$ at the same inventory $x$, $s=1,\dots,t$, then the maximum expected revenue is
--   $$
--   \pi_t(x)=\lambda\sum_{s=1}^t\bigl[m_s(x)-\mu\bigr].\qquad(14)
--   $$
--
--   Under unified pricing the optimal margin $m_t$ is the immediate contribution of a sale, and $\Delta^w\pi_{t-1}$ is the weighted future value of a unit of inventory across in-stock variates.
--
--   **Formalization Note.** The paper's "$t=T,\dots,0$" is taken as $t\ge1$: at $t=0$ there is no $\pi_{-1}$ and $\pi_0=0$ is the boundary condition (4). $S(x)\neq\emptyset$ is assumed, since $a_w$ and $\Delta^w\pi$ are undefined (involve $\ln 0$ and $0/0$) for an empty in-stock set. $\pi_t$ is the unified-pricing value function, a supremum over $r\in[0,\infty)$; the statement asserts attainment and nonnegativity of $r^*_t$, which the paper's proof uses but does not check explicitly. The null price of an out-of-stock variate is modelled by removing it from the choice set.
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), p. 329, Proposition 1, (13)–(14); proof in App. A, pp. 336–337

import Mathlib
import Definitions.Def_SubstitutePricing_Unified_Model

namespace SubstitutePricing.Unified

theorem proposition_1 (M : Model) (hM : M.Assumptions) (t : ℕ) (ht : 1 ≤ t)
    (x : Fin M.n → ℕ) (hx : (M.S x).Nonempty) :
    (∃! m : ℝ, M.marginLHS m = M.sigmaU t x) ∧
    (∀ m : ℝ, M.marginLHS m = M.sigmaU t x →
      0 ≤ M.deltaW t x + m ∧
      IsMaxOn (M.objU (M.piU (t - 1)) x) (Set.Ici 0) (M.deltaW t x + m) ∧
      M.piU t x = M.objU (M.piU (t - 1)) x (M.deltaW t x + m) ∧
      m * M.P0 x (M.const (M.deltaW t x + m)) = M.μ) ∧
    (∀ ms : ℕ → ℝ, (∀ s ∈ Finset.Icc 1 t, M.marginLHS (ms s) = M.sigmaU s x) →
      M.piU t x = M.lam * ∑ s ∈ Finset.Icc 1 t, (ms s - M.μ)) := by sorry

end SubstitutePricing.Unified
