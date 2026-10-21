-- Prove2me | Theorems.Thm_TechSourcing_PTS_lemma_A1_equity
-- name    : TechSourcing.PTS.lemma_A1_equity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:41.033913+00:00
-- url     : https://prove2.me/theorems/afd976e9-7c4d-4b76-9924-4fdde4b95a78
-- title:
--   Lemma A.1 (A-3), p. Appendix-11 — given φ, the optimal equity PTS is θ̂E(φ) = π(φ)/(3/a + 3/b + √(9a² + 10ab + b²)/(ab))
-- statement:
--   Fix the existing supplier's cost $\varphi\le1$ and let $\pi(\varphi)=D[R-\beta(R-\varphi)]$. Under the standing assumptions, suppose
--   $$\hat\theta_E(\varphi)=\frac{\pi(\varphi)}{\dfrac3a+\dfrac3b+\dfrac{\sqrt{9a^2+10ab+b^2}}{ab}}\in(0,1).$$
--   Then
--
--   1. the manufacturer has a best response to $\varphi$ in the equity game, i.e. an admissible equity outcome (IC, IR, fair valuation) maximizing its payoff $U_E$ over all admissible outcomes; and
--   2. every such best response induces the PTS $\theta=\hat\theta_E(\varphi)$.
--
--   This is the equity half of Lemma A.1: the optimal PTS "for the new supplier and the manufacturer" given $\varphi$. Combined with the existing supplier's best response (A-5) it yields the equity equilibrium of Lemma 1.
-- source:
--   Zhang & Lee, Investment Strategies for Sourcing a New Technology in the Presence of a Mature Technology, SSRN 3269249 (version of 23 Mar 2021), p. Appendix-11 (PDF 37), Lemma A.1, (A-3)

import Mathlib
import Definitions.Def_TechSourcing_PTS_Model

namespace TechSourcing.PTS

/-- Lemma A.1, (A-3) (p. Appendix-11): given `φ ≤ 1` with `θ̂_E(φ) ∈ (0, 1)`, the manufacturer has
an optimal equity contract, and every optimal equity outcome has PTS `θ̂_E(φ)`. -/
theorem lemma_A1_equity (P : Params) (hP : P.Standing) (φ : ℝ) (hφ : φ ≤ 1)
    (h0 : 0 < thetaHatE P φ) (h1 : thetaHatE P φ < 1) :
    (∃ o : EqOutcome, IsManufBR_E P φ o) ∧
      ∀ o : EqOutcome, IsManufBR_E P φ o → o.θ = thetaHatE P φ := by sorry
end TechSourcing.PTS
