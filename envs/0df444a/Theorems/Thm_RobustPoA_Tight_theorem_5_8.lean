-- Prove2me | Theorems.Thm_RobustPoA_Tight_theorem_5_8
-- name    : RobustPoA.Tight.theorem_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:50:04.778632+00:00
-- url     : https://prove2.me/theorems/4f65c113-e3dd-4331-a1ee-c46348f6d418
-- title:
--   Theorem 5.8, p. 30, equation (34), p. 23 — congestion games form a tight class
-- statement:
--   Fix any nonempty set $\mathcal C$ of nonnegative, nondecreasing resource cost functions, with the irrelevant all-zero function excluded. Let $\mathcal G(\mathcal C)$ be the class of all finite congestion games whose resource costs lie in $\mathcal C$. The class is tight:
--
--   $$\sup_{G\in\mathcal G(\mathcal C)}\rho_{\mathrm{pure}}(G)
--   =\inf_{(\lambda,\mu)\in\mathcal A(\mathcal G(\mathcal C))}\frac{\lambda}{1-\mu}.$$
--
--   Thus the best uniform smoothness bound for this game class is attained as a supremal pure-equilibrium inefficiency. Together with the paper's extension theorem, the same worst-case bound applies to broader equilibrium notions.
--
--   **Formalization Note** The supremum ranges over all natural numbers of players and resources. Only feasible profiles enter smoothness and the optimum. Both sides use $[0,\infty]$: an empty smoothness-parameter set has infimum $+\infty$, and a positive equilibrium cost with zero optimum gives infinite POA. Any pair admissible for the whole class has a nonnegative ratio, so the conversion from real to extended nonnegative values does not weaken the equality. The restriction on all-zero functions is the standing convention of §5.1.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), Theorem 5.8, p. 30; equation (34), p. 23

import Definitions.Def_RobustPoA_Tight_Classes

namespace RobustPoA.Tight

open scoped ENNReal

/-- Theorem 5.8, p. 30, stated as (34), p. 23: for every nonempty class of
nonnegative, nondecreasing, nonzero cost functions, the congestion-game class is tight. -/
theorem theorem_5_8 (C : Set (ℕ → ℝ)) (hne : C.Nonempty)
    (hC : ∀ c ∈ C, IsCostFn c) :
    worstPoA C =
      ⨅ p ∈ classParams C, ENNReal.ofReal (p.1 / (1 - p.2)) := by sorry

end RobustPoA.Tight
