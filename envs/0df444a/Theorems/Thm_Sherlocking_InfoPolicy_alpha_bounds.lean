-- Prove2me | Theorems.Thm_Sherlocking_InfoPolicy_alpha_bounds
-- name    : Sherlocking.InfoPolicy.alpha_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:27.781988+00:00
-- url     : https://prove2.me/theorems/59b4d94f-4762-4dca-838c-39b5c146a576
-- title:
--   §4, p. 13 (PDF 15) — 0 ≤ α(θ; r) < 1 on [θ_P(r), 1], and 0 < θ_S(r) ≤ θ_P(r) ≤ 1
-- statement:
--   Let $\delta<1$ and $K$ satisfy Assumption 1, $1-\delta<K<\delta$, and let the referral fee satisfy $0\le r<1-K$. Let $\theta_S(r)=\min\{K/(1-r),1\}$ and $\theta_P(r)=\min\{K/(\delta(1-r)),1\}$ be the cutoffs (1)–(2), and $\alpha(\theta;r)=\frac1\delta\big(1-\frac{K}{(1-r)\theta}\big)$ the binding entry probability of §4. Then
--   $$0<\theta_S(r)\le\theta_P(r)\le1,$$
--   and for every $\theta\in[\theta_P(r),1]$,
--   $$0\le\alpha(\theta;r)<1 .$$
--
--   This is the paper's remark that $\alpha$ is a probability, read on the range where it is used: the full-commitment policy applies $\alpha$ exactly on $[\theta_P(r),1]$, and $\alpha$ is negative below $K/(1-r)$. The cutoff ordering makes the integration limits of $\Pi^C_P$, (OC0) and (4) correctly ordered.
--
--   **Formalization Note** The hypotheses $\delta<1$ (the period lengths $1-\delta$ and $\delta$ are positive) and $r<1-K$ (equivalently $\theta_S(r)<1$, so that some type enters) are added; the paper's fee range is $r\in[0,1]$.
-- source:
--   Choi, Kim & Mukherjee, “Sherlocking” and Platform Information Policy, CESifo Working Paper No. 10769 / SSRN 4643950 (version of November 13, 2023), p. 13 (PDF 15), §4, unnumbered remark after the formula for α(θ; r)

import Mathlib
import Definitions.Def_Sherlocking_InfoPolicy_Model

namespace Sherlocking.InfoPolicy

theorem alpha_bounds (K δ r : ℝ) (hδ1 : δ < 1) (hK1 : 1 - δ < K) (hK2 : K < δ) (hr0 : 0 ≤ r) (hrK : r < 1 - K) : (0 < thetaS K r ∧ thetaS K r ≤ thetaP K δ r ∧ thetaP K δ r ≤ 1) ∧ ∀ θ ∈ Set.Icc (thetaP K δ r) 1, 0 ≤ alpha K δ θ r ∧ alpha K δ θ r < 1 := by sorry

end Sherlocking.InfoPolicy
