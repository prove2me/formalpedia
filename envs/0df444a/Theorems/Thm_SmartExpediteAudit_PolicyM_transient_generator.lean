-- Prove2me | Theorems.Thm_SmartExpediteAudit_PolicyM_transient_generator
-- name    : SmartExpediteAudit.PolicyM.transient_generator
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-09T09:08:04.67495+00:00
-- url     : https://prove2.me/theorems/e98aa1d6-7d92-4636-b013-330846263693
-- title:
--   Uniformized Policy-M transition law has the operational rates as its generator
-- statement:
--   For the Policy-M rates with $K\ge1$, $\lambda>0$ and $\mu_k>0$ ($1\le k\le K$), let $P_t$ be the uniformized transition law $P_t(x,n)=\sum_{r\ge0} e^{-ct}\frac{(ct)^r}{r!}U^r(x,n)$. Then for all states $x,n$,
--
--   $$\lim_{t\downarrow 0}\frac{P_t(x,n)-\delta_{xn}}{t}=q(x,n)-\delta_{xn}\,q(x),$$
--
--   where $q(x,n)$ is the Policy-M transition rate and $q(x)$ the total outflow rate.
--
--   Role: this is the generator conjunct of the parent, identifying the Poisson mixture as the chain with the operational rates of (8).
-- source:
--   Song et al., SSRN 3702068, September 28, 2020 version, https://ssrn.com/abstract=3702068, (8), p. 15; uniformization as in S. M. Ross, Stochastic Processes, 2nd ed., Wiley 1996, Section 5.8

import Mathlib
import Definitions.Def_SmartExpediteAudit_PolicyM_Transient

open SmartExpedite.PolicyM
open scoped NNReal Topology

namespace SmartExpediteAudit.PolicyM

theorem transient_generator (K : ℕ) (u : ℕ → ℕ → ℕ∞) (lam : ℝ) (mu : ℕ → ℝ)
    (hK : 1 ≤ K) (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k) :
    ∀ x n, Filter.Tendsto
      (fun t : ℝ≥0 =>
        (transient K u lam mu t x n - (if x = n then 1 else 0)) / (t : ℝ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (rate K u lam mu x n -
        if x = n then outRate K lam mu x else 0)) := by sorry

end SmartExpediteAudit.PolicyM
