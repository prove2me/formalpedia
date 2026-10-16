-- Prove2me | Theorems.Thm_RiskEU_RobustShrink_proposition_2_1
-- name    : RiskEU.RobustShrink.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:00.154178+00:00
-- url     : https://prove2.me/theorems/79006d2b-0966-4cdb-88ac-032b52ed1960
-- title:
--   Proposition 2(1), p. 16 — variance decreases with sample size
-- statement:
--   Fix $N\geq2$, $\gamma>0$, $\sigma_g^2>0$, $\psi^2\geq0$, and a shrinkage intensity $\kappa\in[0,1]$. For each sample size $T>N+7$, the closed-form out-of-sample utility variance $V_T(\kappa)$ from Proposition 1 strictly decreases when the sample size rises by one. Moreover,
--   $$
--   V_{T+1}(\kappa)<V_T(\kappa),\qquad \lim_{T\to\infty}V_T(\kappa)=0.
--   $$
--   This controls the sampling risk for every fixed admissible shrinkage intensity.
--
--   **Formalization Note** The OOSU mean and variance are the closed forms from Proposition IA.1 and Proposition 1. Their identification with the moments of the random portfolio utility is established by those results and is outside this closed-form mission.
-- source:
--   Lassance, Martín-Utrera, Simaan, The Risk of Expected Utility under Parameter Uncertainty, SSRN 3855546 (version dated August 18, 2023), Proposition 2(1), p. 16; Section IA.10, proof of Proposition 2, p. IA39

import Mathlib
import Definitions.Def_RiskEU_RobustShrink_Setting

namespace RiskEU.RobustShrink

/-- Proposition 2(1), p. 16: OOSU variance decreases with sample size and tends to zero. -/
theorem proposition_2_1 (p : Params) (hp : p.Standing) (kappa : ℝ)
    (hkappa : kappa ∈ Set.Icc (0 : ℝ) 1) :
    (∀ T : ℕ, p.N + 7 < T → p.oosuVar (T + 1) kappa < p.oosuVar T kappa) ∧
      Filter.Tendsto (fun T : ℕ => p.oosuVar T kappa) Filter.atTop (nhds 0) := by sorry

end RiskEU.RobustShrink
