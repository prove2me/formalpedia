-- Prove2me | Theorems.Thm_SmartExpediteAudit_PolicyM_transient_semigroup
-- name    : SmartExpediteAudit.PolicyM.transient_semigroup
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-09T09:07:29.526509+00:00
-- url     : https://prove2.me/theorems/5b0ae1f5-15b6-4bfa-8255-bef340b29161
-- title:
--   Uniformized Policy-M transition law satisfies the Chapman-Kolmogorov semigroup identity
-- statement:
--   For the Policy-M rates with $K\ge1$, $\lambda>0$ and $\mu_k>0$ ($1\le k\le K$), let $P_t(x,n)=\sum_{r\ge0} e^{-ct}\frac{(ct)^r}{r!}\,U^r(x,n)$ be the transition law obtained by uniformizing the rates with the clock rate $c=2(\lambda+\sum_k\mu_k)$ and kernel $U$. Then for all $s,t\ge0$ and states $x,n$,
--
--   $$\sum_{y} P_s(x,y)\,P_t(y,n)=P_{s+t}(x,n),$$
--
--   with the series convergent.
--
--   Role: this is the semigroup (Chapman-Kolmogorov) conjunct of the parent, certifying that the Poisson mixture is a continuous-time transition semigroup.
-- source:
--   Song et al., SSRN 3702068, September 28, 2020 version, https://ssrn.com/abstract=3702068, (8), p. 15; uniformization as in S. M. Ross, Stochastic Processes, 2nd ed., Wiley 1996, Section 5.8

import Mathlib
import Definitions.Def_SmartExpediteAudit_PolicyM_Transient

open SmartExpedite.PolicyM
open scoped NNReal Topology

namespace SmartExpediteAudit.PolicyM

theorem transient_semigroup (K : ℕ) (u : ℕ → ℕ → ℕ∞) (lam : ℝ) (mu : ℕ → ℝ)
    (hK : 1 ≤ K) (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k) :
    ∀ s t x n, HasSum (fun y : Fin K → ℕ =>
      transient K u lam mu s x y * transient K u lam mu t y n)
        (transient K u lam mu (s + t) x n) := by sorry

end SmartExpediteAudit.PolicyM
