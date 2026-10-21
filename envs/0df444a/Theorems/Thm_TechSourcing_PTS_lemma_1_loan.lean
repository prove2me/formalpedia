-- Prove2me | Theorems.Thm_TechSourcing_PTS_lemma_1_loan
-- name    : TechSourcing.PTS.lemma_1_loan
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:42.8266+00:00
-- url     : https://prove2.me/theorems/98af8e10-d4bd-4e7a-9d03-6ce3ed1c19a9
-- title:
--   Lemma 1 (7), p. 13 — every loan equilibrium with θ < 1 has PTS θ*L = [√((1 + 3a/b − (a/2)L)² + 6a(W − L)) − (1 + 3a/b − (a/2)L)]/6
-- statement:
--   Let $W(\beta)=[(1-\beta)R+\beta]D$ and $L(\beta)=D^2(1-\beta)\beta/(2c)$, and assume the standing assumptions and $W(\beta)>L(\beta)$. Put
--   $$\theta^*_L=\frac{\sqrt{\big(1+\tfrac{3a}{b}-\tfrac a2L(\beta)\big)^2+6a\big(W(\beta)-L(\beta)\big)}-\big(1+\tfrac{3a}{b}-\tfrac a2L(\beta)\big)}{6}.$$
--   Then
--
--   1. every equilibrium $(o,\varphi)$ of the loan game (interest normalized to $0$) whose PTS is uncertain ($\theta<1$) has PTS $\theta=\theta^*_L$ and existing-supplier cost $\varphi=1-D(1-\beta)(1-\theta^*_L)/(2c)$; and
--   2. if $0<\theta^*_L<1$, a loan equilibrium exists.
--
--   The paper's further claim $\partial\theta^*_L/\partial a>0$ is not part of this statement.
-- source:
--   Zhang & Lee, Investment Strategies for Sourcing a New Technology in the Presence of a Mature Technology, SSRN 3269249 (version of 23 Mar 2021), p. 13 (PDF 13), Lemma 1, (7); W(β) > L(β) assumed from p. 14; θ < 1 from p. 13

import Mathlib
import Definitions.Def_TechSourcing_PTS_Model

namespace TechSourcing.PTS

/-- Lemma 1, (7) (p. 13): if `W(β) > L(β)`, every loan equilibrium with an uncertain R&D
(`θ < 1`) has PTS `θ*_L` and existing-supplier cost `φ(θ*_L)`; and a loan equilibrium exists
whenever `θ*_L ∈ (0, 1)`. -/
theorem lemma_1_loan (P : Params) (hP : P.Standing) (hWL : Lb P < Wb P) :
    (∀ (o : LoanOutcome) (φ : ℝ), IsLoanEq P o φ → o.θ < 1 →
        o.θ = thetaLStar P ∧ φ = phiHat P (thetaLStar P)) ∧
      (0 < thetaLStar P → thetaLStar P < 1 → ∃ (o : LoanOutcome) (φ : ℝ), IsLoanEq P o φ) := by sorry
end TechSourcing.PTS
