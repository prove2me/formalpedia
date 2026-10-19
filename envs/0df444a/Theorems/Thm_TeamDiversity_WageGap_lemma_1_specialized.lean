-- Prove2me | Theorems.Thm_TeamDiversity_WageGap_lemma_1_specialized
-- name    : TeamDiversity.WageGap.lemma_1_specialized
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:14.844159+00:00
-- url     : https://prove2.me/theorems/a3426a34-34ce-40d1-8c3d-4af01d70a996
-- title:
--   Lemma 1 (k = s), p. 12 — δ^m ∈ (0,1), and w_s* is the (shirk, shirk) wage for δ ≥ δ^m and (1−δ)c/(f_s(2)−f_s(1)) for δ < δ^m
-- statement:
--   Under the standing assumptions, the threshold $\delta^m = \frac{2f_s(1)-f_s(2)-f_s(0)}{f_s(1)-f_s(0)}$ lies in $(0,1)$. Moreover, for every $\delta \in [0,1]$, the least specialized wage satisfying $w_s \ge 0$, (IR) and the piecewise (M-IC) constraint of the specialized program (without the No-cycling constraint) is
--
--   $$w_s^* = \begin{cases} \dfrac{c}{(1-\delta)\big(f_s(2)-f_s(1)\big)+\delta\big(f_s(2)-f_s(0)\big)} & \text{if } \delta \ge \delta^m, \\[2ex] \dfrac{(1-\delta)c}{f_s(2)-f_s(1)} & \text{if } \delta < \delta^m. \end{cases}$$
--
--   This is the specialized half of Lemma 1. Below $\delta^m$ specialized teams punish a deviation by (work, shirk), above it by (shirk, shirk).
--
--   **Formalization Note** The optimal contract is the least element of the feasible set.
-- source:
--   Glover & Kim, Optimal Team Composition: Diversity to Foster Implicit Team Incentives, SSRN working paper 3344922 (June 2020 version), p. 12 (PDF 13), Lemma 1 (case k = s, and δ^m ∈ (0,1)); program 1) of Appendix A without (No-cycling), p. 31 (PDF 32)

import Mathlib
import Definitions.Def_TeamDiversity_WageGap_Model

namespace TeamDiversity.WageGap

/-- Lemma 1 (k = s), p. 12: `δ^m ∈ (0,1)` and the optimal mutual-monitoring wage of a
specialized team, `(shirk, shirk)` form for `δ ≥ δ^m` and `(work, shirk)` form for `δ < δ^m`. -/
theorem lemma_1_specialized (c : ℝ) (fs fd : Tech) (hst : Standing c fs fd) :
    0 < deltaM fs ∧ deltaM fs < 1 ∧
      ∀ δ ∈ Set.Icc (0 : ℝ) 1,
        IsLeast (FeasSMM c fs δ)
          (if deltaM fs ≤ δ then c / ((1 - δ) * (fs.f2 - fs.f1) + δ * (fs.f2 - fs.f0))
           else (1 - δ) * c / (fs.f2 - fs.f1)) := by sorry

end TeamDiversity.WageGap
