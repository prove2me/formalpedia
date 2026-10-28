-- Prove2me | Theorems.Thm_Sherlocking_InfoPolicy_cutoffs_monotone
-- name    : Sherlocking.InfoPolicy.cutoffs_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:17.777154+00:00
-- url     : https://prove2.me/theorems/b86bdbf9-277b-43ea-900a-dd0d9e942239
-- title:
--   §4, p. 13 (PDF 15) — θ_P(r), θ_S(r) increasing in r; α(θ; r) decreasing in r and increasing in θ
-- statement:
--   Let $\delta<1$ and $K$ satisfy Assumption 1, $1-\delta<K<\delta$. With the cutoffs $\theta_S(r)=\min\{K/(1-r),1\}$, $\theta_P(r)=\min\{K/(\delta(1-r)),1\}$ and $\alpha(\theta;r)=\frac1\delta\big(1-\frac{K}{(1-r)\theta}\big)$:
--
--   1. $\theta_P$ is nondecreasing on $[0,1]$ and strictly increasing on $[0,\,1-K/\delta)$, where $\theta_P(r)<1$;
--   2. $\theta_S$ is nondecreasing on $[0,1]$ and strictly increasing on $[0,\,1-K)$, where $\theta_S(r)<1$;
--   3. for every $\theta>0$, $r\mapsto\alpha(\theta;r)$ is strictly decreasing on $[0,1)$;
--   4. for every $r\in[0,1)$, $\theta\mapsto\alpha(\theta;r)$ is strictly increasing on $(0,\infty)$.
--
--   In formulas, for $0\le r<r'$ in the stated ranges,
--   $$\theta_P(r)<\theta_P(r'),\qquad \theta_S(r)<\theta_S(r'),\qquad \alpha(\theta;r)>\alpha(\theta;r').$$
--
--   These comparative statics drive the paper's discussion of how the fee trades off seller entry against the platform's entry.
--
--   **Formalization Note** The cutoffs are constant equal to $1$ once the minimum is attained, so on all of $[0,1]$ they are only weakly increasing; strict monotonicity is stated on the range where the minimum is the fraction. $\delta<1$ is added as in the rest of the mission.
-- source:
--   Choi, Kim & Mukherjee, “Sherlocking” and Platform Information Policy, CESifo Working Paper No. 10769 / SSRN 4643950 (version of November 13, 2023), p. 13 (PDF 15), §4, unnumbered remark after the formula for α(θ; r)

import Mathlib
import Definitions.Def_Sherlocking_InfoPolicy_Model

namespace Sherlocking.InfoPolicy

theorem cutoffs_monotone (K δ : ℝ) (hδ1 : δ < 1) (hK1 : 1 - δ < K) (hK2 : K < δ) : MonotoneOn (fun r => thetaP K δ r) (Set.Icc 0 1) ∧ StrictMonoOn (fun r => thetaP K δ r) (Set.Ico 0 (1 - K / δ)) ∧ MonotoneOn (fun r => thetaS K r) (Set.Icc 0 1) ∧ StrictMonoOn (fun r => thetaS K r) (Set.Ico 0 (1 - K)) ∧ (∀ θ : ℝ, 0 < θ → StrictAntiOn (fun r => alpha K δ θ r) (Set.Ico 0 1)) ∧ (∀ r ∈ Set.Ico (0:ℝ) 1, StrictMonoOn (fun θ => alpha K δ θ r) (Set.Ioi 0)) := by sorry

end Sherlocking.InfoPolicy
