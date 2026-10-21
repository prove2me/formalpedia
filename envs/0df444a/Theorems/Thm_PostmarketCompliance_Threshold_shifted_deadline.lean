-- Prove2me | Theorems.Thm_PostmarketCompliance_Threshold_shifted_deadline
-- name    : PostmarketCompliance.Threshold.shifted_deadline
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:09.33456+00:00
-- url     : https://prove2.me/theorems/adbd1b29-4cee-4033-af81-937be2cb8075
-- title:
--   Proof of Proposition 2 — higher enforceability improves the fixed-effort compliance margin
-- statement:
--   Keep all model parameters except withdrawal enforceability fixed. If $s_2>s_1>0$, $\lambda>0$, and $d_1\in[0,T]$, then some deadline $d_2\in[0,T]$ gives a strictly larger fixed-effort profit advantage over never completing the study:
--
--   $$
--   \Pi_{s_2}(\lambda,d_2,\theta)-\Pi_{N,s_2}(d_2)
--   >\Pi_{s_1}(\lambda,d_1,\theta)-\Pi_{N,s_1}(d_1).
--   $$
--
--   The assertion applies to any real $\theta$; the mission’s compliance conclusions use $\theta>0$. It isolates the shifted-deadline comparison in the proof of Proposition 2.
--
--   **Formalization Note** The statement keeps the same positive effort when comparing the two enforceability rates. Its strict inequality includes the case $d_1$ lies after the crossing time, by allowing the new deadline to move.
-- source:
--   Xu, Zhao & Petruzzi, Inducing Compliance with Post-Market Studies for Drugs under FDA's Accelerated Approval Pathway, SSRN 3471632 (version of March 2019), p. 39 (PDF 40), proof of Proposition 2

import Mathlib
import Definitions.Def_PostmarketCompliance_Threshold_Model

namespace PostmarketCompliance.Threshold

theorem shifted_deadline (P : Params) (hP : P.Standing)
    (s₂ d₁ θ lam : ℝ) (hs : P.s < s₂)
    (hd : d₁ ∈ Set.Icc (0 : ℝ) P.T) (hlam : 0 < lam) :
    ∃ d₂ ∈ Set.Icc (0 : ℝ) P.T,
      profit P d₁ θ lam - profitN P d₁ <
        profit { P with s := s₂ } d₂ θ lam -
          profitN { P with s := s₂ } d₂ := by sorry

end PostmarketCompliance.Threshold
