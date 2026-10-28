-- Prove2me | Theorems.Thm_TeleDriving_AsymLimited_theorem_2A
-- name    : TeleDriving.AsymLimited.theorem_2A
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:56.356988+00:00
-- url     : https://prove2.me/theorems/ee10dc8d-90d0-4fc4-8069-8b4216694af9
-- title:
--   Theorem 2.A, p. 22 — for m_λ = ⌊αλs⌋, α ∈ (0, 1): liminf max_n SL(m_λ, n)/SL(m_λ, m_λ) ≥ 2 − α
-- statement:
--   Consider the ride-hailing system with remote drivers whose service rate is (4), $\mu(m,q) = [s/\sqrt{m-q+1}+s]^{-1}$, with expected trip time $s > 0$. Scale the fleet with demand as $m_\lambda = \lfloor\alpha\lambda s\rfloor$ for a fixed $\alpha \in (0,1)$ (the supply-limited regime). Let $SL(m,n) = 1-\pi_{m,n}(n)$ be the service level with $m$ vehicles and $n$ remote drivers. Then
--   $$\liminf_{\lambda\to\infty}\ \Big[\max_{n\in\{1,\dots,m_\lambda\}}\frac{SL(m_\lambda,n)}{SL(m_\lambda,m_\lambda)}\Big] \ \ge\ 2-\alpha.$$
--
--   In a large supply-limited market, choosing the number of remote drivers optimally raises the service level, relative to one driver per vehicle, by a factor of at least $2-\alpha$; the gain vanishes as $\alpha \to 1$, consistent with the intermediate regime of Theorem 2.B.
--
--   **Formalization Note** The liminf is stated in $\varepsilon$-form: for every $\varepsilon > 0$, for all sufficiently large $\lambda$, the maximal ratio is at least $2-\alpha-\varepsilon$. The maximum ranges over $n \in \{1,\dots,m_\lambda\}$ only; $m_\lambda \ge 1$ for large $\lambda$.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), p. 22, Theorem 2.A; proof App. D.1, pp. 44–46

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

namespace TeleDriving.AsymLimited

theorem theorem_2A (s alpha : ℝ) (hs : 0 < s) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ lam in Filter.atTop,
      2 - alpha - ε ≤ TeleDriving.ScarceFleet.maxSLRatio (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) := by sorry

end TeleDriving.AsymLimited
