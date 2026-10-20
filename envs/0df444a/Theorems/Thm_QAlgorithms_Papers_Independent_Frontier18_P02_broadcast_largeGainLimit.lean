-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P02_broadcast_largeGainLimit
-- name    : QAlgorithms.Papers.Independent.Frontier18.P02.broadcast_largeGainLimit
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:49:10.688181+00:00
-- url     : https://prove2.me/theorems/d0939236-de74-473f-8535-861655a0f6d3
-- title:
--   Equation (67): large-gain broadcast linear trade-off
-- statement:
--   Let $N_S>0$ and $N_B\ge0$ be finite real photon numbers. Write $g(x)=(x+1)\log_2(x+1)-x\log_2x$ for $x\ge0$, with $0\log_2 0=0$. For every $\lambda\in[0,1]$, define the explicit Bob and Charlie boundary functions from (40) and (41) by
--   $$
--   B_\kappa(\lambda)=g(\kappa\lambda N_S+(\kappa-1)(N_B+1))-g((\kappa-1)(N_B+1)),
--   $$
--   $$
--   C_\kappa(\lambda)=g((\kappa-1)(N_S+1)+\kappa N_B)-g((\kappa-1)(\lambda N_S+1)+\kappa N_B).
--   $$
--   Then
--   $$
--   \lim_{\kappa\to\infty}B_\kappa(\lambda)=\log_2\!\left(1+\frac{\lambda N_S}{N_B+1}\right),\qquad
--   \lim_{\kappa\to\infty}C_\kappa(\lambda)=\log_2\!\left(\frac{N_S+N_B+1}{\lambda N_S+N_B+1}\right).
--   $$
--   The union of the nonnegative rectangles below these limiting boundary pairs is exactly
--   $$
--   \{(R_B,R_C)\in\mathbb R_{\ge0}^2:R_B+R_C\le\log_2(1+N_S/(N_B+1))\}.
--   $$
--
--   These pointwise limits and the exact union describe the gain-independent linear trade-off in (67). They concern the explicit achievable-region functions; for nonzero thermal noise they do not claim an unconditional operational capacity equality.
-- source:
--   Capacities of Quantum Amplifier Channels, arXiv:1605.04922v3, PDF p. 8, Equation (67): large-gain broadcast linear trade-off

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier18.P02

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

/-- PDF pp.8--9, (67): pointwise large-gain limits of (40)--(41), including
lambda=0 and lambda=1, and their exact parametrization of the nonnegative
linear trade-off triangle. For noise>0 this is a limit of explicit achievable
bounds; it does not assert an unconditional operational capacity formula. -/
theorem broadcast_largeGainLimit (budget noise : ℝ)
    (hbudget : 0 < budget) (hnoise : 0 ≤ noise) :
    (∀ lambda : ℝ, 0 ≤ lambda → lambda ≤ 1 →
      Tendsto (fun gain : ℝ => broadcastBobBoundary gain budget noise lambda)
        atTop (nhds (Real.logb 2 (1 + lambda * budget / (noise + 1)))) ∧
      Tendsto (fun gain : ℝ => broadcastCharlieBoundary gain budget noise lambda)
        atTop (nhds (Real.logb 2 ((budget + noise + 1) /
          (lambda * budget + noise + 1))))) ∧
    {rates : ℝ × ℝ | 0 ≤ rates.1 ∧ 0 ≤ rates.2 ∧
      ∃ lambda : ℝ, 0 ≤ lambda ∧ lambda ≤ 1 ∧
        rates.1 ≤ Real.logb 2 (1 + lambda * budget / (noise + 1)) ∧
        rates.2 ≤ Real.logb 2 ((budget + noise + 1) /
          (lambda * budget + noise + 1))} =
    {rates : ℝ × ℝ | 0 ≤ rates.1 ∧ 0 ≤ rates.2 ∧
      rates.1 + rates.2 ≤ Real.logb 2 (1 + budget / (noise + 1))} := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P02

end
