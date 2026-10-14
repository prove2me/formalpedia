-- Prove2me | Theorems.Thm_TeleDriving_AsymIntermediate_appD2_mode_ratio_tendsto
-- name    : TeleDriving.AsymIntermediate.appD2_mode_ratio_tendsto
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:56.796304+00:00
-- url     : https://prove2.me/theorems/2bca3b40-2129-4dd3-9ab3-c4850ca1964a
-- title:
--   App. D.2, p. 46 — π_{m_λ,m_λ}(⌊q₁⌋)/π_{m_λ,m_λ}(m_λ) = 1/Π ρ(k) → ∞
-- statement:
--   Let $s > 0$ and $1 < \alpha < 2$, use the service rate (4), and let $m_\lambda = \lfloor \alpha\lambda s\rfloor$. Suppose $q_1(\lambda) < q_2(\lambda)$ are, for all sufficiently large $\lambda$, two solutions of $\rho(q) = 1$ (with $m = m_\lambda$) satisfying $\lambda s \le q_1(\lambda) < q_2(\lambda) \le m_\lambda$. Consider the system with as many drivers as vehicles, $n = m_\lambda$. Then for all large $\lambda$
--   $$\frac{\pi_{m_\lambda,m_\lambda}(\lfloor q_1\rfloor)}{\pi_{m_\lambda,m_\lambda}(m_\lambda)} = \frac{1}{\prod_{k=\lfloor q_1\rfloor+1}^{m_\lambda}\rho(k)} = \frac{1}{\Bigl[\prod_{k=\lfloor q_1\rfloor+1}^{\lfloor q_2\rfloor}\rho(k)\Bigr]\Bigl[\prod_{k=\lfloor q_2\rfloor+1}^{m_\lambda}\rho(k)\Bigr]},$$
--   and this ratio tends to $+\infty$ as $\lambda \to \infty$.
--
--   In the intermediate regime the stationary distribution of the system with $n = m$ is bimodal, with modes at $\lfloor q_1\rfloor$ and at $m$; the statement says that the lower mode dominates the upper one, which is the reduction the paper uses to prove Theorem 2.B.
--
--   **Formalization Note** The roots are characterized for all large $\lambda$ only, as in Steps (i)–(ii). Divergence to $+\infty$ is `Tendsto … atTop atTop`. The two identities are the paper's display from (2)–(3); they are asserted for all large $\lambda$.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), App. D.2, Proof of Theorem 2.B, p. 46

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

namespace TeleDriving.AsymIntermediate

theorem appD2_mode_ratio_tendsto (s alpha : ℝ) (hs : 0 < s) (ha1 : 1 < alpha) (ha2 : alpha < 2)
    (q1 q2 : ℝ → ℝ)
    (hq : ∀ᶠ lam in Filter.atTop,
      lam * s ≤ q1 lam ∧ q1 lam < q2 lam ∧ q2 lam ≤ (TeleDriving.ScarceFleet.mLam alpha s lam : ℝ) ∧
      TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) (q1 lam) = 1 ∧
      TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) (q2 lam) = 1) :
    (∀ᶠ lam in Filter.atTop,
      TeleDriving.ScarceFleet.piMN (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) (TeleDriving.ScarceFleet.mLam alpha s lam) ⌊q1 lam⌋₊ /
          TeleDriving.ScarceFleet.piMN (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) (TeleDriving.ScarceFleet.mLam alpha s lam) (TeleDriving.ScarceFleet.mLam alpha s lam) =
        1 / ∏ k ∈ Finset.Ioc ⌊q1 lam⌋₊ (TeleDriving.ScarceFleet.mLam alpha s lam),
          TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) (k : ℝ) ∧
      1 / ∏ k ∈ Finset.Ioc ⌊q1 lam⌋₊ (TeleDriving.ScarceFleet.mLam alpha s lam),
          TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) (k : ℝ) =
        1 / ((∏ k ∈ Finset.Ioc ⌊q1 lam⌋₊ ⌊q2 lam⌋₊,
            TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) (k : ℝ)) *
          (∏ k ∈ Finset.Ioc ⌊q2 lam⌋₊ (TeleDriving.ScarceFleet.mLam alpha s lam),
            TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) (k : ℝ)))) ∧
    Filter.Tendsto
      (fun lam : ℝ =>
        TeleDriving.ScarceFleet.piMN (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) (TeleDriving.ScarceFleet.mLam alpha s lam) ⌊q1 lam⌋₊ /
          TeleDriving.ScarceFleet.piMN (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) (TeleDriving.ScarceFleet.mLam alpha s lam) (TeleDriving.ScarceFleet.mLam alpha s lam))
      Filter.atTop Filter.atTop := by sorry

end TeleDriving.AsymIntermediate
