-- Prove2me | Theorems.Thm_TechSourcing_PTS_thetaLStar_rewrite
-- name    : TechSourcing.PTS.thetaLStar_rewrite
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:26.257979+00:00
-- url     : https://prove2.me/theorems/4d32d82a-b29d-4478-af73-efe0d6df0cf6
-- title:
--   Proof of Proposition 1, p. Appendix-13 — θ*L = (W − L)/(√((1/a + 3/b − L/2)² + (6/a)(W − L)) + 1/a + 3/b − L/2)
-- statement:
--   Under the standing assumptions and $W(\beta)>L(\beta)$, the loan PTS (7) can be rewritten as
--   $$\theta^*_L=\frac{W(\beta)-L(\beta)}{\sqrt{\big(\tfrac1a+\tfrac3b-\tfrac12L(\beta)\big)^2+\tfrac6a\big(W(\beta)-L(\beta)\big)}+\tfrac1a+\tfrac3b-\tfrac12L(\beta)} .$$
--
--   This puts $\theta^*_L$ in the same "numerator $W-L$ over a denominator" shape as $\theta^*_E$ in (6), which is how the two are compared in Proposition 1.
-- source:
--   Zhang & Lee, Investment Strategies for Sourcing a New Technology in the Presence of a Mature Technology, SSRN 3269249 (version of 23 Mar 2021), p. Appendix-13 (PDF 39), proof of Proposition 1 ("First, we can rewrite θ*L as")

import Mathlib
import Definitions.Def_TechSourcing_PTS_Model

namespace TechSourcing.PTS

/-- Proof of Proposition 1 (p. Appendix-13): `θ*_L` rewritten as
`(W − L)/(√((1/a + 3/b − L/2)² + (6/a)(W − L)) + 1/a + 3/b − L/2)`. -/
theorem thetaLStar_rewrite (P : Params) (hP : P.Standing) (hWL : Lb P < Wb P) :
    thetaLStar P = (Wb P - Lb P) /
      (Real.sqrt ((1 / P.a + 3 / P.b - 1 / 2 * Lb P) ^ 2 + 6 / P.a * (Wb P - Lb P))
        + 1 / P.a + 3 / P.b - 1 / 2 * Lb P) := by sorry
end TechSourcing.PTS
