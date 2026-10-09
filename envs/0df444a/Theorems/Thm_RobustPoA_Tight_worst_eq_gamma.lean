-- Prove2me | Theorems.Thm_RobustPoA_Tight_worst_eq_gamma
-- name    : RobustPoA.Tight.worst_eq_gamma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:49:47.643967+00:00
-- url     : https://prove2.me/theorems/2afacb08-7008-45a9-bbec-0f37ddd3fae8
-- title:
--   §5.5, p. 32 — worst pure POA equals γ(C)
-- statement:
--   For every nonempty class $\mathcal C$ of admissible resource cost functions, the worst pure price of anarchy over all finite congestion games using functions from $\mathcal C$ equals the best resourcewise smoothness bound:
--
--   $$\sup_{G\in\mathcal G(\mathcal C)}\rho_{\mathrm{pure}}(G)=\gamma(\mathcal C).$$
--
--   This is the first characterization stated after Theorem 5.8 and gives a way to express the worst-case value through the constraints (35).
--
--   **Formalization Note** The equality is in $[0,\infty]$ and includes classes with a function that has a zero at a positive load.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), §5.5, p. 32, first characterization following Theorem 5.8

import Definitions.Def_RobustPoA_Tight_Classes

namespace RobustPoA.Tight

open scoped ENNReal

/-- §5.5, p. 32: the worst pure price of anarchy for a cost-function class is
the best resourcewise smoothness bound `γ(C)`. -/
theorem worst_eq_gamma (C : Set (ℕ → ℝ)) (hne : C.Nonempty)
    (hC : ∀ c ∈ C, IsCostFn c) : worstPoA C = gamma C := by sorry

end RobustPoA.Tight
