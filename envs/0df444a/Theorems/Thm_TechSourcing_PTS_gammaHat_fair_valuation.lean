-- Prove2me | Theorems.Thm_TechSourcing_PTS_gammaHat_fair_valuation
-- name    : TechSourcing.PTS.gammaHat_fair_valuation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:32.079198+00:00
-- url     : https://prove2.me/theorems/624ac376-e245-4407-970c-4d00f206f36b
-- title:
--   Proof of Lemma A.1, p. Appendix-20 — fair valuation forces the equity share γ̂ = (3(a + b) − √(9a² + 10ab + b²))/(4b)
-- statement:
--   In the equity game, fix the existing supplier's cost $\varphi\le1$ and write $\pi(\varphi)=D[R-\beta(R-\varphi)]$ and
--   $$\hat\theta_E(\varphi)=\frac{\pi(\varphi)}{3/a+3/b+\sqrt{9a^2+10ab+b^2}/(ab)} .$$
--   Assume the standing assumptions and $0<\hat\theta_E(\varphi)<1$. Then every best response of the manufacturer to $\varphi$ (an admissible equity outcome maximizing the manufacturer's payoff, with the share $\gamma$ fixed by the fair valuation $\gamma\,\Pi^N_E=B$) carries the equity share
--   $$\gamma=\hat\gamma=\frac{3(a+b)-\sqrt{9a^2+10ab+b^2}}{4b},$$
--   which depends neither on $\varphi$ nor on the induced PTS.
--
--   The share $\hat\gamma$ enters the denominator of (A-3) and (6) through $(6-4\hat\gamma)/a+6/b=3/a+3/b+\sqrt{9a^2+10ab+b^2}/(ab)$, and the comparison function of Proposition 1.
-- source:
--   Zhang & Lee, Investment Strategies for Sourcing a New Technology in the Presence of a Mature Technology, SSRN 3269249 (version of 23 Mar 2021), pp. Appendix-20–21 (PDF 46–47), proof of Lemma A.1 ("fair valuation requires that γ̂Pθ̂ = B")

import Mathlib
import Definitions.Def_TechSourcing_PTS_Model

namespace TechSourcing.PTS

/-- Proof of Lemma A.1 (pp. Appendix-20–21): when the optimal equity PTS `θ̂_E(φ)` lies in
`(0, 1)`, fair valuation forces every optimal equity contract to carry the share
`γ̂ = (3(a + b) − √(9a² + 10ab + b²))/(4b)`. -/
theorem gammaHat_fair_valuation (P : Params) (hP : P.Standing) (φ : ℝ) (hφ : φ ≤ 1)
    (h0 : 0 < thetaHatE P φ) (h1 : thetaHatE P φ < 1) (o : EqOutcome)
    (ho : IsManufBR_E P φ o) : o.γ = gammaHat P := by sorry
end TechSourcing.PTS
