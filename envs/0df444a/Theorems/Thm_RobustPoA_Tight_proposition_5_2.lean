-- Prove2me | Theorems.Thm_RobustPoA_Tight_proposition_5_2
-- name    : RobustPoA.Tight.proposition_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:50:09.707693+00:00
-- url     : https://prove2.me/theorems/63980490-07bb-475a-9ef8-f0ad73f0be9c
-- title:
--   Proposition 5.2, p. 24 — γ(C) bounds each game’s robust price of anarchy
-- statement:
--   Let $\mathcal C$ be a nonempty set of admissible resource cost functions, and let $G$ be any congestion game whose resource costs lie in $\mathcal C$. Then
--
--   $$\rho(G)\le\gamma(\mathcal C),$$
--
--   where $\rho(G)$ is the best smoothness ratio for that game and $\gamma(\mathcal C)$ is the best ratio from the resourcewise constraints (35). This makes $\gamma(\mathcal C)$ a uniform robust price-of-anarchy bound for the class.
--
--   **Formalization Note** Both values are extended nonnegative reals. The class requires a nonempty strategy set for each player.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), Proposition 5.2, p. 24

import Definitions.Def_RobustPoA_Tight_Classes

namespace RobustPoA.Tight

open scoped ENNReal
open CongestionPoA.AsymSum

/-- Proposition 5.2, p. 24: the robust price of anarchy of any game in the class
is bounded by the resourcewise best smoothness ratio. -/
theorem proposition_5_2 (C : Set (ℕ → ℝ)) (hne : C.Nonempty)
    (hC : ∀ c ∈ C, IsCostFn c) {k m : ℕ}
    (G : CongestionGame (Fin k) (Fin m)) (hG : InClass C G) :
    robustPoACG G ≤ gamma C := by sorry

end RobustPoA.Tight
