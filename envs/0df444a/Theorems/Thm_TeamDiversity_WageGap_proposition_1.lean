-- Prove2me | Theorems.Thm_TeamDiversity_WageGap_proposition_1
-- name    : TeamDiversity.WageGap.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:18.544056+00:00
-- url     : https://prove2.me/theorems/1252dcd5-5ba2-4594-8f3e-6047ce9cae67
-- title:
--   Proposition 1, p. 15 — if f_s(0)/f_s(2) > f_d(0)/f_d(2), then E[w_s*] > E[w_d*] and E[w_s*] − E[w_d*] is strictly decreasing in δ
-- statement:
--   Assume the standing assumptions and
--   $$\frac{f_s(0)}{f_s(2)} > \frac{f_d(0)}{f_d(2)}.$$
--   For each $\delta \in [0,1]$ let $w_s^*(\delta)$ be the least feasible wage of the specialized mutual-monitoring program ((IR) and the piecewise (M-IC), without No-cycling) and $w_d^*(\delta)$ the least feasible wage of the diverse program. Then
--
--   1. $E[w_s^*] = f_s(2)\,w_s^*(\delta) > f_d(2)\,w_d^*(\delta) = E[w_d^*]$ for every $\delta \in [0,1]$;
--   2. the gap $\delta \mapsto E[w_s^*] - E[w_d^*]$ is strictly decreasing on $[0,1]$.
--
--   Absent collusion, specialized teams are always more expensive to incentivize, but their disadvantage shrinks as the agents become more patient.
--
--   **Formalization Note** "Monotone decreasing" is read as strictly decreasing.
-- source:
--   Glover & Kim, Optimal Team Composition: Diversity to Foster Implicit Team Incentives, SSRN working paper 3344922 (June 2020 version), p. 15 (PDF 16), Proposition 1

import Mathlib
import Definitions.Def_TeamDiversity_WageGap_Model

namespace TeamDiversity.WageGap

/-- Proposition 1, p. 15: if `f_s(0)/f_s(2) > f_d(0)/f_d(2)`, then `E[w_s*] > E[w_d*]` and the gap
`E[w_s*] − E[w_d*]` of the mutual-monitoring expected wages is strictly decreasing in `δ`. -/
theorem proposition_1 (c : ℝ) (fs fd : Tech) (hst : Standing c fs fd)
    (hratio : fs.f0 / fs.f2 > fd.f0 / fd.f2) (wsMM wd : ℝ → ℝ)
    (hwsMM : ∀ δ ∈ Set.Icc (0 : ℝ) 1, IsLeast (FeasSMM c fs δ) (wsMM δ))
    (hwd : ∀ δ ∈ Set.Icc (0 : ℝ) 1, IsLeast (FeasD c fd δ) (wd δ)) :
    (∀ δ ∈ Set.Icc (0 : ℝ) 1, expWage fs (wsMM δ) > expWage fd (wd δ)) ∧
      StrictAntiOn (fun δ => expWage fs (wsMM δ) - expWage fd (wd δ)) (Set.Icc 0 1) := by sorry

end TeamDiversity.WageGap
