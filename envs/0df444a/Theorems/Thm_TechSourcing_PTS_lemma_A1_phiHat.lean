-- Prove2me | Theorems.Thm_TechSourcing_PTS_lemma_A1_phiHat
-- name    : TechSourcing.PTS.lemma_A1_phiHat
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:33.459288+00:00
-- url     : https://prove2.me/theorems/4e434e9a-badc-40ec-b3f6-0b3c1c15747b
-- title:
--   (A-5), Lemma A.1, p. Appendix-12 — the existing supplier's best response φ̂(θ) = 1 − D(1 − β)(1 − θ)/(2c)
-- statement:
--   Consider the existing supplier, who chooses its final unit production cost $\varphi\le1$ at the additional cost $c(1-\varphi)^2$, anticipating the new supplier's probability of technical success $\theta$. Its payoff is
--   $$U^O(\varphi\mid\theta)=(1-\theta)(1-\beta)(R-\varphi)D-c(1-\varphi)^2 .$$
--   Under the standing assumptions ($a,b,c,D>0$, $R>1$, $\beta\in[0,1]$), for every $\theta\le1$ the cost $\varphi\le1$ maximizes $U^O(\cdot\mid\theta)$ over $\varphi'\le1$ if and only if
--   $$\varphi=\hat\varphi(\theta)=1-\frac{D(1-\beta)(1-\theta)}{2c}.$$
--
--   The same best response serves both the equity and the loan game, because the existing supplier's payoff has the same form in both.
-- source:
--   Zhang & Lee, Investment Strategies for Sourcing a New Technology in the Presence of a Mature Technology, SSRN 3269249 (version of 23 Mar 2021), p. Appendix-12 (PDF 38), Lemma A.1, (A-5)

import Mathlib
import Definitions.Def_TechSourcing_PTS_Model

namespace TechSourcing.PTS

/-- (A-5), Lemma A.1 (p. Appendix-12): given a PTS `θ ≤ 1`, the existing supplier's unique
best response is `φ̂(θ) = 1 − D(1 − β)(1 − θ)/(2c)`. -/
theorem lemma_A1_phiHat (P : Params) (hP : P.Standing) (θ : ℝ) (hθ : θ ≤ 1) (φ : ℝ) :
    IsExistingBR P θ φ ↔ φ = phiHat P θ := by sorry
end TechSourcing.PTS
