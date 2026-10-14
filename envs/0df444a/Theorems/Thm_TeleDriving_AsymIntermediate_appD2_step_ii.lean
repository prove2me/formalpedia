-- Prove2me | Theorems.Thm_TeleDriving_AsymIntermediate_appD2_step_ii
-- name    : TeleDriving.AsymIntermediate.appD2_step_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:53.973979+00:00
-- url     : https://prove2.me/theorems/b598bc43-d570-4c71-8430-97421951ec71
-- title:
--   App. D.2, Step (ii), p. 47 — Π_{k=⌊q₁⌋+1}^{⌊q₂⌋} ρ(k) → 0 as λ → ∞
-- statement:
--   Let $s > 0$ and $1 < \alpha < 2$, use the service rate (4), and let $m_\lambda = \lfloor \alpha\lambda s\rfloor$. Suppose $q_1(\lambda) < q_2(\lambda)$ are, for all sufficiently large $\lambda$, two solutions of $\rho(q) = 1$ (with $m = m_\lambda$) satisfying $\lambda s \le q_1(\lambda) < q_2(\lambda) \le m_\lambda$. Then the product of the loads between the two roots vanishes:
--   $$\lim_{\lambda\to\infty} \prod_{k=\lfloor q_1\rfloor+1}^{\lfloor q_2\rfloor} \rho(k) = 0 .$$
--
--   This is the second step of the proof of Theorem 2.B: between the two roots every load is below one, and the stretch is long enough that the product vanishes.
--
--   **Formalization Note** As in Step (i), the roots are functions of $\lambda$ characterized for all large $\lambda$ only; for large $\lambda$ they coincide with the paper's $q_1, q_2$. The product runs over the integers $k$ with $\lfloor q_1\rfloor < k \le \lfloor q_2\rfloor$, with $\rho$ evaluated at $k$.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), App. D.2, Proof of Theorem 2.B, Step (ii), p. 47

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

namespace TeleDriving.AsymIntermediate

theorem appD2_step_ii (s alpha : ℝ) (hs : 0 < s) (ha1 : 1 < alpha) (ha2 : alpha < 2)
    (q1 q2 : ℝ → ℝ)
    (hq : ∀ᶠ lam in Filter.atTop,
      lam * s ≤ q1 lam ∧ q1 lam < q2 lam ∧ q2 lam ≤ (TeleDriving.ScarceFleet.mLam alpha s lam : ℝ) ∧
      TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) (q1 lam) = 1 ∧
      TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) (q2 lam) = 1) :
    Filter.Tendsto
      (fun lam : ℝ => ∏ k ∈ Finset.Ioc ⌊q1 lam⌋₊ ⌊q2 lam⌋₊,
        TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) (k : ℝ))
      Filter.atTop (nhds 0) := by sorry

end TeleDriving.AsymIntermediate
