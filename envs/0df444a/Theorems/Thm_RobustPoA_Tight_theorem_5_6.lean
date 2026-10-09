-- Prove2me | Theorems.Thm_RobustPoA_Tight_theorem_5_6
-- name    : RobustPoA.Tight.theorem_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:49:52.988389+00:00
-- url     : https://prove2.me/theorems/6decb0f1-ccce-44a3-88ee-c3375702daf2
-- title:
--   Theorem 5.6, p. 28 — finite-class lower-bound construction
-- statement:
--   Let $\mathcal C$ be a nonempty finite set of strictly positive, nondecreasing cost functions and let $n\ge1$. For every value $b$ strictly below $\gamma(\mathcal C,n)$, there is a congestion game $G$ using only functions in $\mathcal C$ whose pure price of anarchy exceeds $b$:
--
--   $$\forall b<\gamma(\mathcal C,n),\quad\exists G\in\mathcal G(\mathcal C):\ b<\rho_{\mathrm{pure}}(G).$$
--
--   This gives the finite-class lower bound used in Theorem 5.8.
--
--   **Formalization Note** The printed phrase “arbitrarily close” is encoded by this one-sided lower approximation. The proof establishes this direction and does not require two-sided closeness. All finite player and resource counts are allowed.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), Theorem 5.6, p. 28

import Definitions.Def_RobustPoA_Tight_Classes

namespace RobustPoA.Tight

open scoped ENNReal
open CongestionPoA.AsymSum

/-- Theorem 5.6, p. 28: finite positive cost-function classes admit congestion games
whose pure price of anarchy exceeds every strict lower bound on `γ(C,n)`. -/
theorem theorem_5_6 (C : Set (ℕ → ℝ)) (hfinite : C.Finite) (hne : C.Nonempty)
    (hC : ∀ c ∈ C, IsCostFn c ∧ IsStrictlyPos c) (n : ℕ) (hn : 1 ≤ n) :
    ∀ b : ℝ≥0∞, b < gammaN C n →
      ∃ (k m : ℕ) (G : CongestionGame (Fin k) (Fin m)),
        InClass C G ∧ b < purePoA G := by sorry

end RobustPoA.Tight
