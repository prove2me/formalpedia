-- Prove2me | Theorems.Thm_OutpatientWalkIn_SmallCap_lemma_D_3_unobs_exists
-- name    : OutpatientWalkIn.SmallCap.lemma_D_3_unobs_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:31.687734+00:00
-- url     : https://prove2.me/theorems/f5940c92-34cf-4627-ac9b-f82fddfc9171
-- title:
--   Lemma D.3, Online App. p. 11 — an unobservable equilibrium (λ_S, λ_W, λ_B) exists at every allocation 0 ≤ μ_S < μ
-- statement:
--   Assume the standing assumptions of the model. For every allocation $\mu_S$ with $0 \le \mu_S < \mu$, there are rates $(\lambda_S,\lambda_W,\lambda_B)$ that form an equilibrium of the unobservable setting. The rates are nonnegative and sum to $\lambda$. The appointment queue is stable ($\lambda_S<\mu_S$, or $\lambda_S=0$ when $\mu_S=0$). Every option used with positive rate maximizes the utility among
--   $$u^1_S(\lambda_S) = R - C_D\frac{\lambda_S}{2\mu_S(\mu_S-\lambda_S)},\qquad u^1_W(\lambda_W) = R - C_W\,w\Big(\frac{\lambda_W+\lambda_E}{\mu-\mu_S}\Big),\qquad u^1_B = 0,$$
--   with scheduling excluded from the comparison when $\mu_S=0$ (Condition 1).
--
--   This shows that the unobservable side of the goal theorem is not vacuous: an unobservable equilibrium exists at every allocation.
--
--   **Formalization Note** Lemma D.3 gives the equilibrium explicitly in three regimes, through $\lambda^B_S = \min\{2R\mu_S^2/(C_D+2R\mu_S),\lambda\}$, $\lambda^B_W = \max\{\min\{w^{-1}(R/C_W)\mu_W-\lambda_E,\lambda\},0\}$ and the root $\lambda'_S$ of $u^1_S(\lambda'_S) = u^1_W(\lambda-\lambda'_S)$. This item states the existence that the lemma's table implies, without $w^{-1}$ and without that root.
-- source:
--   Liu, van Jaarsveld, Wang, Xiao, Managing Outpatient Service with Strategic Walk-ins, SSRN 3558209 (version of 2022-07-05), Online Appendix p. 11, Lemma D.3 (existence of the triplet), with Condition 1 (p. 13), (18), (19) (p. 23)

import Mathlib
import Definitions.Def_OutpatientWalkIn_SmallCap_MD1Queue
import Definitions.Def_OutpatientWalkIn_SmallCap_Setting

namespace OutpatientWalkIn.SmallCap
theorem lemma_D_3_unobs_exists (M : Model) (hM : M.Standing) (μS : ℝ) (hμS : μS ∈ Set.Ico 0 M.mu) :
    ∃ u : UnobsStrategy, M.IsUnobsEq μS u := by sorry
end OutpatientWalkIn.SmallCap
