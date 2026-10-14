-- Prove2me | Theorems.Thm_TeleDriving_AsymRich_lemma5
-- name    : TeleDriving.AsymRich.lemma5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:05.731011+00:00
-- url     : https://prove2.me/theorems/20cedbe5-3b1d-4690-bd21-d231214ee7b7
-- title:
--   Lemma 5, pp. 47–48 — with n_ϵ = ⌊(1+ϵ)q₃⌋ drivers, the mass outside ((1−ϵ/2)q₃, (1+ϵ/2)q₃) vanishes
-- statement:
--   Let $s > 0$, $\alpha > 2$, $m_\lambda = \lfloor\alpha\lambda s\rfloor$, and let the service rate be (4). Let $q_3(\lambda)$ be, for all sufficiently large $\lambda$, a root of $\rho = 1$ in $[\lambda s, m_\lambda]$ (as in case (iii) of Appendix D). Fix $\epsilon$ with $0 < \epsilon < \alpha - 1$ and put $n_\epsilon = \lfloor (1+\epsilon) q_3 \rfloor$. Then, for the system with $m_\lambda$ vehicles and $n_\epsilon$ remote drivers,
--
--   $$\lim_{\lambda\to\infty} \Bigg[ \sum_{i=\lfloor (1+\epsilon/2) q_3\rfloor}^{n_\epsilon} \pi_{m_\lambda,n_\epsilon}(i) + \sum_{i=0}^{\lfloor (1-\epsilon/2) q_3\rfloor} \pi_{m_\lambda,n_\epsilon}(i) \Bigg] = 0.$$
--
--   So with about $(1+\epsilon)$ times the critical load $q_3$ of drivers, the stationary number of customers in service concentrates in a window of relative width $\epsilon$ around $q_3$; in particular the blocking probability $\pi_{m_\lambda,n_\epsilon}(n_\epsilon)$ vanishes. This is the lemma from which the paper derives Theorem 2.C.
--
--   **Formalization Note** The paper says "for any small $\epsilon > 0$". It is read as $0 < \epsilon < \alpha - 1$: exactly in this range $n_\epsilon \le m_\lambda$ for large $\lambda$ (as $q_3 \sim \lambda s$ and $m_\lambda \sim \alpha\lambda s$), so that $\pi_{m_\lambda,n_\epsilon}$ is the paper's distribution. If $\epsilon \ge 2$, the floor $\lfloor (1-\epsilon/2) q_3\rfloor$ is $0$ (natural-number floor) and the second sum is $\pi_{m_\lambda,n_\epsilon}(0)$. $q_3$ is characterized by an eventually-holding hypothesis rather than by the closed form (17).
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), App. D.3, Lemma 5, pp. 47–48

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

namespace TeleDriving.AsymRich

theorem lemma5 (s alpha : ℝ) (hs : 0 < s) (ha : 2 < alpha) (q3 : ℝ → ℝ)
    (hq3 : ∀ᶠ lam in Filter.atTop, lam * s ≤ q3 lam ∧ q3 lam ≤ (TeleDriving.ScarceFleet.mLam alpha s lam : ℝ) ∧
      TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) (q3 lam) = 1)
    (eps : ℝ) (he0 : 0 < eps) (he1 : eps < alpha - 1) :
    Filter.Tendsto (fun lam : ℝ =>
      ∑ i ∈ Finset.Icc ⌊(1 + eps / 2) * q3 lam⌋₊ ⌊(1 + eps) * q3 lam⌋₊,
          TeleDriving.ScarceFleet.piMN (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) ⌊(1 + eps) * q3 lam⌋₊ i +
        ∑ i ∈ Finset.range (⌊(1 - eps / 2) * q3 lam⌋₊ + 1),
          TeleDriving.ScarceFleet.piMN (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) ⌊(1 + eps) * q3 lam⌋₊ i)
      Filter.atTop (nhds 0) := by sorry

end TeleDriving.AsymRich
