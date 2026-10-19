-- Prove2me | Theorems.Thm_RiskEU_RobustShrink_proposition_IA_1_3
-- name    : RiskEU.RobustShrink.proposition_IA_1_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:01.405992+00:00
-- url     : https://prove2.me/theorems/ee02007b-c888-4ed2-b063-46c6f949c011
-- title:
--   Proposition IA.1(3), p. IA1 — mean-optimal shrinkage intensity
-- statement:
--   For $N\geq2$, $T>N+7$, $\gamma>0$, $\sigma_g^2>0$, and $\psi^2\geq0$, let $E_T(\kappa)$ be the closed-form out-of-sample utility mean in (IA2). The intensity
--   $$
--   \kappa_E(T)=\frac{(T-N)(T-N-3)}{T(T-2)}\frac{\psi^2}{\psi^2+(N-1)/T}
--   $$
--   lies in $[0,1]$ and maximizes $E_T$ over every real intensity $\kappa$. In particular, it maximizes OOSU mean among the admissible shrinkage portfolios.
--
--   This result identifies the mean benchmark used in the robust-intensity ordering.
--
--   **Formalization Note** The OOSU mean and variance are the closed forms from Proposition IA.1 and Proposition 1. Their identification with the moments of the random portfolio utility is established by those results and is outside this closed-form mission.
-- source:
--   Lassance, Martín-Utrera, Simaan, The Risk of Expected Utility under Parameter Uncertainty, SSRN 3855546 (version dated August 18, 2023), Proposition IA.1(3), (IA2)–(IA3), p. IA1

import Mathlib
import Definitions.Def_RiskEU_RobustShrink_Setting

namespace RiskEU.RobustShrink

/-- Proposition IA.1(3), p. IA1: the vertex of the OOSU mean quadratic. -/
theorem proposition_IA_1_3 (p : Params) (hp : p.Standing) (T : ℕ)
    (hT : p.N + 7 < T) :
    p.kappaE T ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ kappa : ℝ, p.oosuMean T kappa ≤ p.oosuMean T (p.kappaE T) := by sorry

end RiskEU.RobustShrink
