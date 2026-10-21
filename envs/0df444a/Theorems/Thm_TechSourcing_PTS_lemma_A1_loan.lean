-- Prove2me | Theorems.Thm_TechSourcing_PTS_lemma_A1_loan
-- name    : TechSourcing.PTS.lemma_A1_loan
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:26.088481+00:00
-- url     : https://prove2.me/theorems/46f16010-750a-403e-945e-7ad31b4bbac4
-- title:
--   Lemma A.1 (A-4), p. Appendix-11 — given φ, the optimal loan PTS is θ̂L(φ) = π(φ)/[√((1/a + 3/b)² + 6π(φ)/a) + (1/a + 3/b)]
-- statement:
--   Fix the existing supplier's cost $\varphi\le1$ and let $\pi(\varphi)=D[R-\beta(R-\varphi)]$. Under the standing assumptions, suppose
--   $$\hat\theta_L(\varphi)=\frac{\pi(\varphi)}{\sqrt{\big(\tfrac1a+\tfrac3b\big)^2+\tfrac{6\pi(\varphi)}{a}}+\tfrac1a+\tfrac3b}\in(0,1).$$
--   Then
--
--   1. the manufacturer has a best response to $\varphi$ in the loan game (interest normalized to $0$), i.e. an admissible loan outcome (IC, IR) maximizing its payoff $U_L$ over all admissible outcomes; and
--   2. every such best response induces the PTS $\theta=\hat\theta_L(\varphi)$.
--
--   This is the loan half of Lemma A.1; with (A-5) it yields the loan equilibrium of Lemma 1.
-- source:
--   Zhang & Lee, Investment Strategies for Sourcing a New Technology in the Presence of a Mature Technology, SSRN 3269249 (version of 23 Mar 2021), p. Appendix-11 (PDF 37), Lemma A.1, (A-4)

import Mathlib
import Definitions.Def_TechSourcing_PTS_Model

namespace TechSourcing.PTS

/-- Lemma A.1, (A-4) (p. Appendix-11): given `φ ≤ 1` with `θ̂_L(φ) ∈ (0, 1)`, the manufacturer has
an optimal loan contract, and every optimal loan outcome has PTS `θ̂_L(φ)`. -/
theorem lemma_A1_loan (P : Params) (hP : P.Standing) (φ : ℝ) (hφ : φ ≤ 1)
    (h0 : 0 < thetaHatL P φ) (h1 : thetaHatL P φ < 1) :
    (∃ o : LoanOutcome, IsManufBR_L P φ o) ∧
      ∀ o : LoanOutcome, IsManufBR_L P φ o → o.θ = thetaHatL P φ := by sorry
end TechSourcing.PTS
