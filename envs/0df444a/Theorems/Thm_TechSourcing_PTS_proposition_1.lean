-- Prove2me | Theorems.Thm_TechSourcing_PTS_proposition_1
-- name    : TechSourcing.PTS.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:51.336412+00:00
-- url     : https://prove2.me/theorems/08fc14d8-3129-4b98-b856-75e8026315e9
-- title:
--   Proposition 1, p. 15 — equity yields a higher equilibrium PTS than a loan iff a > āT(β), and iff β lies outside [β̄L(a), β̄H(a)]
-- statement:
--   Consider the equity and loan games of the model, with the standing assumptions $a,b,c,D>0$, $R>1$, $\beta\in[0,1]$, and the paper's assumption $W(\beta)>L(\beta)$, where $W(\beta)=[(1-\beta)R+\beta]D$ and $L(\beta)=D^2(1-\beta)\beta/(2c)$. Write $\theta^*_E$ and $\theta^*_L$ for the PTS of an equity equilibrium and of a loan equilibrium with an uncertain R&D ($\theta<1$).
--
--   1. **(Technological maturity.)** Fix $b,c,D,R,\beta$ with $W(\beta)>L(\beta)$. There is a threshold $\bar a_T(\beta)\in\mathbb R$ such that, for every $a>0$ and all such equilibria,
--   $$\theta^*_E>\theta^*_L\iff a>\bar a_T(\beta),$$
--   or else equity never yields the strictly higher PTS ($\theta^*_E\le\theta^*_L$ for every $a>0$; the case $\bar a_T(\beta)=+\infty$).
--   2. **(Bargaining power.)** Fix $a,b,c,D,R$. There are reals $\bar\beta_L(a)\le\bar\beta_H(a)$ such that, for every $\beta\in[0,1]$ with $W(\beta)>L(\beta)$ and all such equilibria,
--   $$\theta^*_E>\theta^*_L\iff \beta<\bar\beta_L(a)\ \text{ or }\ \beta>\bar\beta_H(a).$$
--
--   So the profit-sharing effect of equity dominates the cost-shifting effect of a loan when the new technology is mature enough, or when the existing supplier is weak or strong enough.
--
--   **Formalization Note** The statement is about the PTS of Nash equilibria of the two games, not about the closed forms (6), (7). In (i) only $a$ varies ($b$ is held fixed; the paper's remark that $a\propto b$ is not imposed). In (ii) the thresholds are real numbers rather than points of $[0,1]$: the paper notes that "some of the three regions may disappear if $\bar\beta_L(a)$ and/or $\bar\beta_H(a)$ are not between 0 and 1", and requiring them in $[0,1]$ would make the statement false when equity wins for every $\beta$. $W(\beta)>L(\beta)$ is a hypothesis for each $\beta$ in (ii), as it is assumed "hereafter" on p. 14. Equilibria with $\theta<1$ exist whenever the closed forms lie in $(0,1)$ (milestones Lemma 1 (6), (7)).
-- source:
--   Zhang & Lee, Investment Strategies for Sourcing a New Technology in the Presence of a Mature Technology, SSRN 3269249 (version of 23 Mar 2021), p. 15 (PDF 15), Proposition 1 (i)–(ii); proof pp. Appendix-12–13 (PDF 38–39)

import Mathlib
import Definitions.Def_TechSourcing_PTS_Model

namespace TechSourcing.PTS

/-- Proposition 1 (p. 15). (i) Given the bargaining power `β` (and `b, c, D, R`), there is a
threshold `ā_T(β)` such that, for every technological maturity `a > 0`, the equilibrium PTS under
equity exceeds the one under a loan iff `a > ā_T(β)` (or equity never yields the higher PTS,
`ā_T = +∞`). (ii) Given `a` (and `b, c, D, R`), there are `β̄_L(a) ≤ β̄_H(a)` such that, for every
`β ∈ [0, 1]` with `W(β) > L(β)`, the equity PTS exceeds the loan PTS iff `β < β̄_L(a)` or
`β > β̄_H(a)`. Equilibria are those of the equity and loan games with an uncertain R&D (`θ < 1`).
The printed proposition places both β thresholds in `[0, 1]`, but its proof explicitly allows
thresholds outside that interval when a region disappears; this statement follows the proof. -/
theorem proposition_1 :
    (∀ P : Params, P.Standing → Lb P < Wb P →
      (∃ aT : ℝ, ∀ a : ℝ, 0 < a → ∀ (oE : EqOutcome) (φE : ℝ) (oL : LoanOutcome) (φL : ℝ),
          IsEquityEq { P with a := a } oE φE → oE.θ < 1 →
          IsLoanEq { P with a := a } oL φL → oL.θ < 1 →
          (oL.θ < oE.θ ↔ aT < a)) ∨
      (∀ a : ℝ, 0 < a → ∀ (oE : EqOutcome) (φE : ℝ) (oL : LoanOutcome) (φL : ℝ),
          IsEquityEq { P with a := a } oE φE → oE.θ < 1 →
          IsLoanEq { P with a := a } oL φL → oL.θ < 1 → oE.θ ≤ oL.θ)) ∧
    (∀ P : Params, P.Standing →
      ∃ βL βH : ℝ, βL ≤ βH ∧ ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
        Lb { P with β := β } < Wb { P with β := β } →
        ∀ (oE : EqOutcome) (φE : ℝ) (oL : LoanOutcome) (φL : ℝ),
          IsEquityEq { P with β := β } oE φE → oE.θ < 1 →
          IsLoanEq { P with β := β } oL φL → oL.θ < 1 →
          (oL.θ < oE.θ ↔ β < βL ∨ βH < β)) := by sorry
end TechSourcing.PTS
