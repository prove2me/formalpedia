-- Prove2me | Theorems.Thm_TeamDiversity_WageGap_threshold_bounds
-- name    : TeamDiversity.WageGap.threshold_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:13.792667+00:00
-- url     : https://prove2.me/theorems/c592bf4b-8d5e-4430-a609-500bde45046d
-- title:
--   Proof of Lemma 3, p. 36, and p. 16 — δ^m < 1/2, δ^C > √(1/2), δ^m < δ^C and δ^C < 1
-- statement:
--   Under the standing assumptions,
--
--   $$\delta^m < \tfrac12, \qquad \delta^C > \sqrt{\tfrac12}, \qquad \delta^m < \delta^C, \qquad \delta^C < 1,$$
--
--   where $\delta^m = \frac{2f_s(1)-f_s(2)-f_s(0)}{f_s(1)-f_s(0)}$ and $\delta^C = \sqrt{\frac{f_s(2)-f_s(1)}{f_s(1)-f_s(0)}}$.
--
--   These place the collusion threshold $\delta^C$ strictly inside $(\delta^m, 1)$, so that for specialized teams the punishment switch happens before collusion becomes binding.
-- source:
--   Glover & Kim, Optimal Team Composition: Diversity to Foster Implicit Team Incentives, SSRN working paper 3344922 (June 2020 version), proof of Lemma 3, p. 36 (PDF 37) (δ^m < 1/2, δ^C > √(1/2)) and p. 37 (PDF 38) (δ^C > δ^m); p. 16 (PDF 17) (δ^C < 1)

import Mathlib
import Definitions.Def_TeamDiversity_WageGap_Model

namespace TeamDiversity.WageGap

/-- Proof of Lemma 3, pp. 36–37, and p. 16: `δ^m < 1/2`, `δ^C > √(1/2)`, hence `δ^m < δ^C`,
and `δ^C < 1`. -/
theorem threshold_bounds (c : ℝ) (fs fd : Tech) (hst : Standing c fs fd) :
    deltaM fs < 1 / 2 ∧ Real.sqrt (1 / 2) < deltaC fs ∧ deltaM fs < deltaC fs ∧
      deltaC fs < 1 := by sorry

end TeamDiversity.WageGap
