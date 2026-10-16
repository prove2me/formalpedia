-- Prove2me | Theorems.Thm_RiskEU_RobustShrink_proposition_IA_1_limit
-- name    : RiskEU.RobustShrink.proposition_IA_1_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:05.39097+00:00
-- url     : https://prove2.me/theorems/45c314c1-dfc5-42da-933c-1b557c455f65
-- title:
--   Proposition IA.1, p. IA2 — mean-optimal intensity tends to one
-- statement:
--   Fix the number of stocks $N$, risk aversion $\gamma$, population variances $\sigma_g^2$ and $\psi^2$, GMV mean $\mu_g$, and robustness weight $\lambda$. If $N\geq2$, $\gamma>0$, $\sigma_g^2>0$, and $\psi^2>0$, then the mean-maximizing intensity in (IA3) obeys
--   $$
--   \lim_{T\to\infty}\kappa_E(T)=1.
--   $$
--   This gives the asymptotic mean benchmark for the robust shrinkage intensity.
--
--   **Formalization Note** The paper omits the necessary condition $\psi^2>0$: at $\psi^2=0$, formula (IA3) gives $\kappa_E(T)=0$. The estimator-consistency sentence requires a sample-portfolio model and is outside this closed-form result. The OOSU moments are the closed forms from Proposition IA.1 and Proposition 1; their probabilistic identification is outside this mission.
-- source:
--   Lassance, Martín-Utrera, Simaan, The Risk of Expected Utility under Parameter Uncertainty, SSRN 3855546 (version dated August 18, 2023), Proposition IA.1, final sentence, p. IA2

import Mathlib
import Definitions.Def_RiskEU_RobustShrink_Setting

namespace RiskEU.RobustShrink

/-- Proposition IA.1, final sentence, p. IA2: the mean-optimal intensity tends to one. -/
theorem proposition_IA_1_limit (p : Params) (hp : p.Standing)
    (hpsi : 0 < p.psi2) :
    Filter.Tendsto (fun T : ℕ => p.kappaE T) Filter.atTop (nhds 1) := by sorry

end RiskEU.RobustShrink
