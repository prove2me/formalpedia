-- Prove2me | Theorems.Thm_PostmarketCompliance_Threshold_proposition_2
-- name    : PostmarketCompliance.Threshold.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:15.167809+00:00
-- url     : https://prove2.me/theorems/d5c72fb1-61de-4ad2-bb03-b160efcb1a7d
-- title:
--   Proposition 2 — compliance threshold increases with enforceability and success probability
-- statement:
--   Fix a post-market study model with horizon $T$, profit rates $\pi_A,\pi_R$, sample size $n$, and cost exponent $k$. Let $\hat\theta(s,\alpha)$ be the supremum of positive manufacturer cost types for which some feasible deadline makes a positive recruitment effort optimal. With the other model parameters fixed, the threshold is nondecreasing in both withdrawal enforceability $s$ and study success probability $\alpha$:
--
--   $$
--    s_1\le s_2\Rightarrow\hat\theta(s_1,\alpha)\le\hat\theta(s_2,\alpha),
--    \qquad
--    \alpha_1\le\alpha_2\Rightarrow\hat\theta(s,\alpha_1)\le\hat\theta(s,\alpha_2).
--   $$
--
--   If some positive cost type complies under the smaller parameter, either strict parameter increase gives a strict threshold increase. Thus stronger enforcement or a more promising study can induce compliance from costlier manufacturers.
--
--   **Formalization Note** The standing regime is $T>0$, $0<\pi_A\le\pi_R$, $0<\alpha\le1$, $s>0$, and $1\le k<n$. An empty compliant-type set has real supremum zero; strictness is therefore guarded by nonemptiness.
-- source:
--   Xu, Zhao & Petruzzi, Inducing Compliance with Post-Market Studies for Drugs under FDA's Accelerated Approval Pathway, SSRN 3471632 (version of March 2019), p. 12 (PDF 13), Proposition 2; proof pp. 39–40 (PDF 40–41)

import Mathlib
import Definitions.Def_PostmarketCompliance_Threshold_Model

namespace PostmarketCompliance.Threshold

theorem proposition_2 (P : Params) (hP : P.Standing) :
    (∀ s₂ : ℝ, P.s ≤ s₂ →
      thetaHat P ≤ thetaHat { P with s := s₂ }) ∧
    (∀ α₂ : ℝ, P.alpha ≤ α₂ → α₂ ≤ 1 →
      thetaHat P ≤ thetaHat { P with alpha := α₂ }) ∧
    ((compliantTypes P).Nonempty →
      (∀ s₂ : ℝ, P.s < s₂ →
        thetaHat P < thetaHat { P with s := s₂ }) ∧
      (∀ α₂ : ℝ, P.alpha < α₂ → α₂ ≤ 1 →
        thetaHat P < thetaHat { P with alpha := α₂ })) := by sorry

end PostmarketCompliance.Threshold
