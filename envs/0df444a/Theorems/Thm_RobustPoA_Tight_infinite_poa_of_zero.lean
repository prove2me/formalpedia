-- Prove2me | Theorems.Thm_RobustPoA_Tight_infinite_poa_of_zero
-- name    : RobustPoA.Tight.infinite_poa_of_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:49:45.374069+00:00
-- url     : https://prove2.me/theorems/04eeca01-bc04-49e9-a378-8ba855810935
-- title:
--   Proof of Theorem 5.8, p. 30 — zero cost at a positive load gives infinite POA
-- statement:
--   Let $c$ be a nonnegative, nondecreasing resource cost function that is nonzero at some positive load but vanishes at another positive load. Then a finite congestion game using only $c$ has an infinite pure price of anarchy:
--
--   $$\exists G\in\mathcal G(\{c\}):\quad\rho_{\mathrm{pure}}(G)=+\infty.$$
--
--   This covers the part of Theorem 5.8 in which the cost-function class contains a function that is not strictly positive.
--
--   **Formalization Note** The game's optimum has cost zero while a pure Nash equilibrium has positive cost; the extended nonnegative quotient preserves the infinite ratio.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), proof of Theorem 5.8, first paragraph, p. 30

import Definitions.Def_RobustPoA_Tight_Classes

namespace RobustPoA.Tight

open scoped ENNReal
open CongestionPoA.AsymSum

/-- Proof of Theorem 5.8, first paragraph, p. 30: a nonzero, nondecreasing cost
function with a zero at some positive load yields a game of infinite pure POA. -/
theorem infinite_poa_of_zero (c : ℕ → ℝ) (hc : IsCostFn c)
    (hzero : ¬ IsStrictlyPos c) :
    ∃ (k m : ℕ) (G : CongestionGame (Fin k) (Fin m)),
      InClass ({c} : Set (ℕ → ℝ)) G ∧ purePoA G = ⊤ := by sorry

end RobustPoA.Tight
