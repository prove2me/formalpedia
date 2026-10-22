-- Prove2me | Theorems.Thm_RiskPostpone_Threshold_proposition_4_i
-- name    : RiskPostpone.Threshold.proposition_4_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:47:39.854184+00:00
-- url     : https://prove2.me/theorems/85b0448b-cf0f-487f-a901-c64098aced98
-- title:
--   Proposition 4(i) (boundary η = η* corrected) — ex ante and responsive pricing share one CVaR risk-aversion threshold η*
-- statement:
--   In the random-yield model with its standing assumptions (in particular $p_0\ge c/\mu$), assume Assumption 2. There is a single risk-aversion threshold $\eta^*\in[0,1]$, with either $\eta^*=0$ or
--   $$
--   p_0\,g(\eta^*)=c,\qquad g(\eta)=\frac1\eta\int_l^{G^{-1}(\eta)}\xi\,dG(\xi),
--   $$
--   such that for every risk level $\eta\in(0,1]$:
--
--   1. the ex ante firm produces at level $\eta$ if and only if $\eta>\eta^*$, and
--   2. the responsive firm produces at level $\eta$ if and only if $\eta>\eta^*$.
--
--   That is, $\eta_a^*(p_0,c)=\eta_r^*(p_0,c)$: postponing the pricing decision until after the yield is observed does not change which risk-averse firms are willing to produce.
--
--   **Formalization Note** "Produces" means some decision has strictly positive CVaR ($p\in[0,p_0]$, $q\ge0$ ex ante; $q\ge0$ responsive). One threshold is shared by both schemes; since a threshold of this form is unique, this is exactly the equality of the two thresholds. At $\eta=\eta^*>0$ the optimal CVaR is $0$, so the strict inequality is the correct boundary. The paper also assumes Assumption 1; it is not used by part (i) and is not assumed. $p_0$ is finite and the yield law has no atoms and full support on $[l,u]$ (no density).
-- source:
--   Kouvelis, Xiao and Yang, Role of Risk Aversion in Price Postponement under Supply Random Yield, accepted manuscript MS-OPM-18-01273.R2 (Management Science 67(8), 2021, doi:10.1287/mnsc.2020.3755), p. 16, Proposition 4(i); proof p. ec9 (PDF 42)

import Mathlib
import Definitions.Def_RiskPostpone_Threshold_Setting

open MeasureTheory Set

namespace RiskPostpone.Threshold

/-- Proposition 4(i) (p. 16; characterization from its proof, p. ec9), boundary `η = η*`
corrected: under Assumption 2 there is one risk-aversion threshold `η* ∈ [0,1]`, equal to `0`
or a root of `p0·g(η) = c`, such that for every `η ∈ (0,1]` the ex ante firm produces iff
`η > η*` and the responsive firm produces iff `η > η*`; i.e. `η*_a = η*_r`. -/
theorem proposition_4_i (M : Model) (hM : M.Standing) (hA2 : M.Assumption2) :
    ∃ ηs ∈ Icc (0 : ℝ) 1, (ηs = 0 ∨ M.p0 * M.tailMean ηs = M.c) ∧
      ∀ η ∈ Ioc (0 : ℝ) 1,
        (M.ProducesExAnte η ↔ ηs < η) ∧ (M.ProducesResponsive η ↔ ηs < η) := by sorry

end RiskPostpone.Threshold
