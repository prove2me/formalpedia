-- Prove2me | Theorems.Thm_RiskEU_RobustShrink_proposition_2_2_kappa
-- name    : RiskEU.RobustShrink.proposition_2_2_kappa
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:02.975578+00:00
-- url     : https://prove2.me/theorems/13631ac3-f1a8-4427-b325-9bba4c6292ce
-- title:
--   Proposition 2(2), κ-clause, p. 16 — variance increases beyond κ*_E
-- statement:
--   Fix $N\geq2$, $T>N+7$, $\gamma>0$, $\sigma_g^2>0$, and $\psi^2\geq0$. Let $\kappa_E(T)$ be the mean-maximizing intensity from (IA3). The closed-form out-of-sample utility variance $V_T(\kappa)$ from Proposition 1 is nondecreasing as $\kappa$ ranges from $\kappa_E(T)$ to $1$:
--   $$
--   \kappa_E(T)\leq\kappa_1\leq\kappa_2\leq1
--   \quad\Longrightarrow\quad V_T(\kappa_1)\leq V_T(\kappa_2).
--   $$
--   This is the risk-side ordering used in Proposition 4.
--
--   **Formalization Note** The source's word “increases” is represented by weak monotonicity, as in its derivative inequality (IA80). Only the shrinkage-intensity clause is formalized. The printed claim of monotonicity in $N$ is false for some admissible parameters; the $\sigma_g^2$ and $\psi^2$ clauses are omitted from this focused item. The moments are the closed forms of Proposition 1 and Proposition IA.1, whose probabilistic identification is outside this mission.
-- source:
--   Lassance, Martín-Utrera, Simaan, The Risk of Expected Utility under Parameter Uncertainty, SSRN 3855546 (version dated August 18, 2023), Proposition 2(2), κ-clause, p. 16; Section IA.10, proof of Proposition 2, (IA80)–(IA88), pp. IA40–IA44

import Mathlib
import Definitions.Def_RiskEU_RobustShrink_Setting

namespace RiskEU.RobustShrink

/-- Proposition 2(2), κ-clause, p. 16: variance is nondecreasing beyond κ*_E. -/
theorem proposition_2_2_kappa (p : Params) (hp : p.Standing) (T : ℕ)
    (hT : p.N + 7 < T) :
    MonotoneOn (p.oosuVar T) (Set.Icc (p.kappaE T) 1) := by sorry

end RiskEU.RobustShrink
