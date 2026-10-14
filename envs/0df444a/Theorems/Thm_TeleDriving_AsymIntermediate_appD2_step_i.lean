-- Prove2me | Theorems.Thm_TeleDriving_AsymIntermediate_appD2_step_i
-- name    : TeleDriving.AsymIntermediate.appD2_step_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:53.63459+00:00
-- url     : https://prove2.me/theorems/172daedf-4945-40e3-abae-d9acfe71de51
-- title:
--   App. D.2, Step (i), p. 47 — m_λ − ⌊q₂⌋ stays bounded and limsup Π_{k=⌊q₂⌋+1}^{m_λ} ρ(k) < ∞
-- statement:
--   Let $s > 0$ and $1 < \alpha < 2$, use the service rate (4), and let $m_\lambda = \lfloor \alpha\lambda s\rfloor$. Suppose $q_1(\lambda) < q_2(\lambda)$ are, for all sufficiently large $\lambda$, two solutions of $\rho(q) = 1$ (with $m = m_\lambda$) satisfying
--   $$\lambda s \le q_1(\lambda) < q_2(\lambda) \le m_\lambda .$$
--   Then the gap $m_\lambda - \lfloor q_2(\lambda)\rfloor$ is bounded for large $\lambda$, and so is the product of the loads above $q_2$:
--   $$\limsup_{\lambda\to\infty}\,\bigl[m_\lambda - \lfloor q_2\rfloor\bigr] < \infty, \qquad \limsup_{\lambda\to\infty} \prod_{k=\lfloor q_2\rfloor+1}^{m_\lambda} \rho(k) < \infty .$$
--
--   This is the first of the two steps of the proof of Theorem 2.B: the large root $q_2$ sits within a bounded distance of the fleet size, so the stretch of the stationary distribution between $q_2$ and $m_\lambda$ contributes only a bounded factor.
--
--   **Formalization Note** For large $\lambda$, $m_\lambda$ lies in the intermediate range of App. D, case (ii), where $\rho = 1$ has exactly two roots in $(0, m_\lambda]$; so the hypothesis pins $q_1, q_2$ down to the paper's $q_1, q_2$ for large $\lambda$. It is required only eventually in $\lambda$ (for small $\lambda$ there are no roots). The two limsup bounds are stated as "there is a constant bounding the quantity for all large $\lambda$". The natural-number subtraction $m_\lambda - \lfloor q_2\rfloor$ does not truncate, since $q_2 \le m_\lambda$.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), App. D.2, Proof of Theorem 2.B, Step (i), p. 47

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

namespace TeleDriving.AsymIntermediate

theorem appD2_step_i (s alpha : ℝ) (hs : 0 < s) (ha1 : 1 < alpha) (ha2 : alpha < 2)
    (q1 q2 : ℝ → ℝ)
    (hq : ∀ᶠ lam in Filter.atTop,
      lam * s ≤ q1 lam ∧ q1 lam < q2 lam ∧ q2 lam ≤ (TeleDriving.ScarceFleet.mLam alpha s lam : ℝ) ∧
      TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) (q1 lam) = 1 ∧
      TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) (q2 lam) = 1) :
    (∃ K : ℕ, ∀ᶠ lam in Filter.atTop, TeleDriving.ScarceFleet.mLam alpha s lam - ⌊q2 lam⌋₊ ≤ K) ∧
    ∃ C : ℝ, ∀ᶠ lam in Filter.atTop,
      ∏ k ∈ Finset.Ioc ⌊q2 lam⌋₊ (TeleDriving.ScarceFleet.mLam alpha s lam),
        TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) (k : ℝ) ≤ C := by sorry

end TeleDriving.AsymIntermediate
