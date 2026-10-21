-- Prove2me | Theorems.Thm_TechSourcing_PTS_comparison
-- name    : TechSourcing.PTS.comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:28.745992+00:00
-- url     : https://prove2.me/theorems/bbe0f20a-51c5-45a1-b298-3d3fb04e5f04
-- title:
--   Proof of Proposition 1, p. Appendix-13 — θ*E ≥ θ*L iff W − [1/3 + (2/3)γ̂]L − (2/3)√(9/b² + 10/(ab) + 1/a²) − 2/(3a) − 2/(3b) ≥ 0
-- statement:
--   Let $\hat\gamma=\big(3(a+b)-\sqrt{9a^2+10ab+b^2}\big)/(4b)$ and
--   $$F=W(\beta)-\Big[\frac13+\frac23\hat\gamma\Big]L(\beta)-\frac23\sqrt{\frac9{b^2}+\frac{10}{ab}+\frac1{a^2}}-\frac2{3a}-\frac2{3b}.$$
--   Under the standing assumptions, $W(\beta)>L(\beta)$, $0<\theta^*_E<1$ and $0<\theta^*_L<1$ (with $\theta^*_E,\theta^*_L$ the closed forms (6), (7)):
--
--   1. $\theta^*_E\ge\theta^*_L$ if and only if $F\ge0$;
--   2. $\theta^*_E>\theta^*_L$ if and only if $F>0$.
--
--   This reduces the comparison of the two equilibrium PTSs to the sign of one explicit function of the parameters, which drives both parts of Proposition 1.
-- source:
--   Zhang & Lee, Investment Strategies for Sourcing a New Technology in the Presence of a Mature Technology, SSRN 3269249 (version of 23 Mar 2021), p. Appendix-13 (PDF 39), proof of Proposition 1 ("With simple algebra, we have θ*E ≥ θ*L if and only if")

import Mathlib
import Definitions.Def_TechSourcing_PTS_Model

namespace TechSourcing.PTS

/-- Proof of Proposition 1 (p. Appendix-13): for `θ*_E, θ*_L ∈ (0, 1)`, `θ*_E ≥ θ*_L` if and only if
`F := W − [1/3 + (2/3)γ̂]L − (2/3)√(9/b² + 10/(ab) + 1/a²) − 2/(3a) − 2/(3b) ≥ 0`, and
`θ*_E > θ*_L` if and only if `F > 0`. -/
theorem comparison (P : Params) (hP : P.Standing) (hWL : Lb P < Wb P)
    (hE0 : 0 < thetaEStar P) (hE1 : thetaEStar P < 1)
    (hL0 : 0 < thetaLStar P) (hL1 : thetaLStar P < 1) :
    (thetaLStar P ≤ thetaEStar P ↔ 0 ≤ Fcmp P) ∧
      (thetaLStar P < thetaEStar P ↔ 0 < Fcmp P) := by sorry
end TechSourcing.PTS
