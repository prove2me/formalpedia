-- Prove2me | Theorems.Thm_PostmarketCompliance_Threshold_alpha_monotonicity
-- name    : PostmarketCompliance.Threshold.alpha_monotonicity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:07.545982+00:00
-- url     : https://prove2.me/theorems/35c590ef-ca8b-4460-9056-f6d3cbceb701
-- title:
--   Proof of Proposition 2 — success probability raises positive-effort profit
-- statement:
--   Keep all model parameters except study success probability fixed. For $0<\alpha_1<\alpha_2\le1$, feasible deadline $d$, and positive effort $\lambda$, positive-effort profit increases strictly while the no-effort benchmark remains the same:
--
--   $$
--   \Pi_{\alpha_1}(\lambda,d,\theta)<\Pi_{\alpha_2}(\lambda,d,\theta),
--   \qquad
--   \Pi_{N,\alpha_1}(d)=\Pi_{N,\alpha_2}(d).
--   $$
--
--   This is the payoff comparison underlying the success-probability part of Proposition 2. The manufacturer benefits from a higher chance of regular approval only if it completes the study.
--
--   **Formalization Note** The comparison fixes $\lambda>0$ and $d\in[0,T]$; cost type $\theta$ may be any real because its effort cost cancels.
-- source:
--   Xu, Zhao & Petruzzi, Inducing Compliance with Post-Market Studies for Drugs under FDA's Accelerated Approval Pathway, SSRN 3471632 (version of March 2019), p. 40 (PDF 41), proof of Proposition 2

import Mathlib
import Definitions.Def_PostmarketCompliance_Threshold_Model

namespace PostmarketCompliance.Threshold

theorem alpha_monotonicity (P : Params) (hP : P.Standing)
    (α₂ d θ lam : ℝ) (hα : P.alpha < α₂) (hα₂ : α₂ ≤ 1)
    (hd : d ∈ Set.Icc (0 : ℝ) P.T) (hlam : 0 < lam) :
    profit P d θ lam < profit { P with alpha := α₂ } d θ lam ∧
    profitN P d = profitN { P with alpha := α₂ } d := by sorry

end PostmarketCompliance.Threshold
