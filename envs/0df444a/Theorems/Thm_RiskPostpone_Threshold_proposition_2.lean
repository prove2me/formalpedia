-- Prove2me | Theorems.Thm_RiskPostpone_Threshold_proposition_2
-- name    : RiskPostpone.Threshold.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:47:33.878724+00:00
-- url     : https://prove2.me/theorems/36a887c1-bbb1-4123-8dfa-025a62b4968c
-- title:
--   Proposition 2 (threshold part; boundary η = η*_a corrected) — the ex ante firm produces iff η > η*_a
-- statement:
--   In the random-yield model with its standing assumptions (in particular $p_0\ge c/\mu$), there is a risk-aversion threshold $\eta_a^*\in[0,1]$, with either $\eta_a^*=0$ or $p_0\,g(\eta_a^*)=c$, such that for every $\eta\in(0,1]$
--   $$
--   \text{the ex ante firm produces at level }\eta\iff \eta>\eta_a^*.
--   $$
--   In particular, if $\eta<\eta_a^*$ it is optimal for the firm not to produce.
--
--   This is the threshold half of Proposition 2: strongly risk-averse ex ante firms do not produce at all.
--
--   **Formalization Note** "Produces" means some price $p\in[0,p_0]$ and quantity $q\ge0$ give strictly positive CVaR; its negation is "not producing is optimal". At $\eta=\eta_a^*>0$ the optimal CVaR is $0$, so the paper's "if $\eta\ge\eta_a^*$ it is optimal to produce" holds only for $\eta>\eta_a^*$; the statement uses the strict inequality. The characterization of $\eta_a^*$ is from the proof (p. ec4). Assumption 1 is not assumed: it is used only for part (ii) (quasi-concavity and the first-order condition), which is not stated here.
-- source:
--   Kouvelis, Xiao and Yang, Role of Risk Aversion in Price Postponement under Supply Random Yield, accepted manuscript MS-OPM-18-01273.R2 (Management Science 67(8), 2021, doi:10.1287/mnsc.2020.3755), p. 10, Proposition 2(i); proof p. ec4 (PDF 37)

import Mathlib
import Definitions.Def_RiskPostpone_Threshold_Setting

open MeasureTheory Set

namespace RiskPostpone.Threshold

/-- Proposition 2, threshold part (p. 10; characterization from its proof, p. ec4): there is a
risk-aversion threshold `η*_a ∈ [0,1]`, equal to `0` or a root of `p0·g(η) = c`, such that for
every `η ∈ (0,1]` the ex ante firm produces (some decision has positive CVaR) iff `η > η*_a`. -/
theorem proposition_2 (M : Model) (hM : M.Standing) :
    ∃ ηa ∈ Icc (0 : ℝ) 1, (ηa = 0 ∨ M.p0 * M.tailMean ηa = M.c) ∧
      ∀ η ∈ Ioc (0 : ℝ) 1, (M.ProducesExAnte η ↔ ηa < η) := by sorry

end RiskPostpone.Threshold
