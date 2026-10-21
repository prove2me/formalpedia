-- Prove2me | Theorems.Thm_TechSourcing_PTS_lemma_1_equity
-- name    : TechSourcing.PTS.lemma_1_equity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:27.685011+00:00
-- url     : https://prove2.me/theorems/9cbb72f9-628f-4e67-acbc-c8b753b38625
-- title:
--   Lemma 1 (6), p. 13 — every equity equilibrium with θ < 1 has PTS θ*E = (W − L)/(3/a + 3/b + √(9a² + 10ab + b²)/(ab) − L)
-- statement:
--   Let $W(\beta)=[(1-\beta)R+\beta]D$ and $L(\beta)=D^2(1-\beta)\beta/(2c)$, and assume the standing assumptions and $W(\beta)>L(\beta)$. Put
--   $$\theta^*_E=\frac{W(\beta)-L(\beta)}{\dfrac3a+\dfrac3b+\dfrac{\sqrt{9a^2+10ab+b^2}}{ab}-L(\beta)},\qquad \varphi(\theta)=1-\frac{D(1-\beta)(1-\theta)}{2c}.$$
--   Then
--
--   1. every equilibrium $(o,\varphi)$ of the equity game whose PTS is uncertain ($\theta<1$) has PTS $\theta=\theta^*_E$ and existing-supplier cost $\varphi=\varphi(\theta^*_E)$; and
--   2. if $0<\theta^*_E<1$, an equity equilibrium exists.
--
--   The paper's further claim $\partial\theta^*_E/\partial a>0$ is not part of this statement.
-- source:
--   Zhang & Lee, Investment Strategies for Sourcing a New Technology in the Presence of a Mature Technology, SSRN 3269249 (version of 23 Mar 2021), p. 13 (PDF 13), Lemma 1, (6); W(β) > L(β) assumed from p. 14; θ < 1 from p. 13

import Mathlib
import Definitions.Def_TechSourcing_PTS_Model

namespace TechSourcing.PTS

/-- Lemma 1, (6) (p. 13): if `W(β) > L(β)`, every equity equilibrium with an uncertain R&D
(`θ < 1`) has PTS `θ*_E` and existing-supplier cost `φ(θ*_E)`; and an equity equilibrium exists
whenever `θ*_E ∈ (0, 1)`. -/
theorem lemma_1_equity (P : Params) (hP : P.Standing) (hWL : Lb P < Wb P) :
    (∀ (o : EqOutcome) (φ : ℝ), IsEquityEq P o φ → o.θ < 1 →
        o.θ = thetaEStar P ∧ φ = phiHat P (thetaEStar P)) ∧
      (0 < thetaEStar P → thetaEStar P < 1 → ∃ (o : EqOutcome) (φ : ℝ), IsEquityEq P o φ) := by sorry
end TechSourcing.PTS
