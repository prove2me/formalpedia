-- Prove2me | Theorems.Thm_PostmarketCompliance_Threshold_profit_representation
-- name    : PostmarketCompliance.Threshold.profit_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:08.010021+00:00
-- url     : https://prove2.me/theorems/f8fc431d-04da-45c0-b36c-26535dd473ae
-- title:
--   Proof of Proposition 1 — profit representation and no-effort closed form
-- statement:
--   For a feasible deadline $d\in[0,T]$ and positive effort $\lambda$, let $g(t,\lambda,n)$ and $G(t,\lambda,n)$ denote the Gamma density and cumulative distribution, and let $R(\lambda,T)$ be the manufacturer’s profit under immediate sanction at deadline $T$. Then
--
--   $$
--   \Pi(\lambda,d,\theta)=R(\lambda,T)-\int_d^T(1-e^{-s(t-d)})\left[\pi_A(1-G(t,\lambda,n))+(T-t)\alpha\pi_Rg(t,\lambda,n)\right]dt,
--   $$
--
--   and, when no study is undertaken,
--
--   $$
--   \Pi_N(d)=d\pi_A+\frac{1-e^{-s(T-d)}}s\pi_A.
--   $$
--
--   The first equation expresses the effect of a delayed withdrawal relative to immediate sanction. The second gives the benchmark used in every compliance comparison.
--
--   **Formalization Note** The equations are restricted to $\lambda>0$ and $0\le d\le T$, with $s>0$ in the standing assumptions. The zero-effort benchmark is defined separately because a rate-zero Gamma measure does not represent noncompletion.
-- source:
--   Xu, Zhao & Petruzzi, Inducing Compliance with Post-Market Studies for Drugs under FDA's Accelerated Approval Pathway, SSRN 3471632 (version of March 2019), p. 38 (PDF 39), proof of Proposition 1

import Mathlib
import Definitions.Def_PostmarketCompliance_Threshold_Model

namespace PostmarketCompliance.Threshold

theorem profit_representation (P : Params) (hP : P.Standing) (d θ lam : ℝ)
    (hd : d ∈ Set.Icc (0 : ℝ) P.T) (hlam : 0 < lam) :
    (profit P d θ lam =
      R P θ lam P.T -
        ∫ t in d..P.T,
          (1 - Real.exp (-(P.s * (t - d)))) *
          (P.piA * (1 - GCdf P lam t) +
            (P.T - t) * P.alpha * P.piR * gPdf P lam t)) ∧
    (profitN P d =
      d * P.piA + (1 / P.s) * (1 - Real.exp (-(P.s * (P.T - d)))) * P.piA) := by sorry

end PostmarketCompliance.Threshold
