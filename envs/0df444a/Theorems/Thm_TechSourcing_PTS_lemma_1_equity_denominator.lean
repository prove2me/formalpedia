-- Prove2me | Theorems.Thm_TechSourcing_PTS_lemma_1_equity_denominator
-- name    : TechSourcing.PTS.lemma_1_equity_denominator
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-02T03:29:10.365243+00:00
-- url     : https://prove2.me/theorems/def2da28-03ed-46ce-8670-cfe737f28554
-- title:
--   Lemma 1 (6), p. 13 — at an equity equilibrium with θ < 1, the denominator of θ*E is positive: L(β) < 3/a + 3/b + √(9a²+10ab+b²)/(ab)
-- statement:
--   Consider the equity game of the model, with the standing assumptions $a,b,c,D>0$, $R>1$, $\beta\in[0,1]$, and suppose $W(\beta)>L(\beta)$, where
--   $$W(\beta)=[(1-\beta)R+\beta]D,\qquad L(\beta)=\frac{D^2(1-\beta)\beta}{2c}.$$
--   Let $(o,\varphi)$ be a Nash equilibrium of the equity game whose probability of technical success (PTS) satisfies $\theta<1$. Then the denominator of formula (6) is positive:
--   $$L(\beta)<\frac{3}{a}+\frac{3}{b}+\frac{\sqrt{9a^2+10ab+b^2}}{ab}.$$
--
--   In Lemma 1 the equilibrium PTS under equity is $\theta^*_E=(W-L)/\big(3/a+3/b+\sqrt{9a^2+10ab+b^2}/(ab)-L\big)$; this statement records that, at any such equilibrium, this expression is well defined with a positive denominator, so that $\theta^*_E>0$.
--
--   **Formalization Note** In Lean division by zero returns $0$, so the milestone formula $o.\theta=\theta^*_E$ alone does not exclude the degenerate case where the denominator of (6) vanishes; this lemma rules it out and is used, together with Lemma 1 and the comparison step of the proof of Proposition 1, to derive Proposition 1.
-- source:
--   Zhang & Lee, Investment Strategies for Sourcing a New Technology in the Presence of a Mature Technology, SSRN 3269249 (version of 23 Mar 2021), p. 13 (PDF 13), Lemma 1 eq. (6); proof via Lemma A.1 (A-3), (A-5), pp. Appendix-11–12 (PDF 37–38)

import Mathlib
import Definitions.Def_TechSourcing_PTS_Model

namespace TechSourcing.PTS

/-- Proof of Lemma 1, (6) (p. 13; proof via Lemma A.1, p. Appendix-12): if `W(β) > L(β)`, then at
every equity equilibrium with an uncertain R&D (`θ < 1`) the denominator of (6) is positive,
`L(β) < 3/a + 3/b + √(9a² + 10ab + b²)/(ab)`. (The equilibrium PTS solves the fixed point
`θ = θ̂_E(φ̂(θ)) = (W − L + Lθ)/(3/a + 3/b + √(9a² + 10ab + b²)/(ab))`, i.e.
`θ·(3/a + 3/b + √(9a² + 10ab + b²)/(ab) − L) = W − L > 0` with `θ ≥ 0`.) -/
theorem lemma_1_equity_denominator (P : Params) (hP : P.Standing) (hWL : Lb P < Wb P)
    (o : EqOutcome) (φ : ℝ) (h : IsEquityEq P o φ) (hθ : o.θ < 1) :
    Lb P < denE P := by sorry
end TechSourcing.PTS
