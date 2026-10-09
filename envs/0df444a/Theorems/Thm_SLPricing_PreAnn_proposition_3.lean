-- Prove2me | Theorems.Thm_SLPricing_PreAnn_proposition_3
-- name    : SLPricing.PreAnn.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:15:22.731364+00:00
-- url     : https://prove2.me/theorems/f7d96074-ad89-4359-b175-a7872db32004
-- title:
--   Proposition 3, p. 17 — under pre-announced pricing, social learning raises optimal profit whenever $\delta_c\le\Delta_{lp}(\gamma)$ or $\delta_c\ge\Delta_{hp}(\gamma)$
-- statement:
--   Assume social learning is present, $\gamma>0$, and fix $\sigma_p$ and $c$. There exist thresholds
--   $$\Delta_{lp}(\gamma)\in(0,1]\qquad\text{and}\qquad\Delta_{hp}(\gamma)\in[0,1)$$
--   such that for every consumer discount factor $\delta_c\in[0,1]$ with $\delta_c\le\Delta_{lp}(\gamma)$ or $\delta_c\ge\Delta_{hp}(\gamma)$, the firm's optimal expected profit under pre-announced pricing with social learning strictly exceeds its optimal expected profit in the absence of social learning:
--   $$\pi_p^*\big|_{\gamma}>\pi_p^*\big|_{\gamma\to 0}.$$
--
--   Social learning makes consumers more strategic (Lemma 2) and a pre-announced price cannot react to the reviews; nevertheless both impatient and patient consumers leave the firm better off with social learning than without it.
--
--   **Formalization Note** Both optimal values are suprema over all real price plans and all their purchasing equilibria, in the extended reals; "absence of SL" is the same model at $\gamma=0$, where the posterior mean is the prior mean $0$. The strict bounds $\Delta_{lp}>0$ and $\Delta_{hp}<1$ are what make the statement non-trivial. The thresholds may depend on $\sigma_p$ and $c$, which are fixed.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), Proposition 3, p. 17; proof, p. 30

import Mathlib
import Definitions.Def_SLPricing_PreAnn_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.PreAnn

/-- Proposition 3, p. 17 (proof p. 30): with social learning (`γ > 0`; `σp`, `c` fixed) there are
thresholds `Δlp ∈ (0, 1]` and `Δhp ∈ [0, 1)` such that for every consumer discount factor
`δc ∈ [0, 1]` with `δc ≤ Δlp` or `δc ≥ Δhp`, the optimal pre-announced profit with social learning
strictly exceeds the optimal pre-announced profit without it (`γ = 0`). -/
theorem proposition_3 (P : Params) (hP : P.Standing) (hγ : 0 < P.γ) :
    ∃ Δlp ∈ Ioc (0 : ℝ) 1, ∃ Δhp ∈ Ico (0 : ℝ) 1, ∀ d ∈ Icc (0 : ℝ) 1, (d ≤ Δlp ∨ Δhp ≤ d) →
      preValue (P.withδc d).noSL < preValue (P.withδc d) := by sorry

end SLPricing.PreAnn
