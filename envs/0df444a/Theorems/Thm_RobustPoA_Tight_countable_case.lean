-- Prove2me | Theorems.Thm_RobustPoA_Tight_countable_case
-- name    : RobustPoA.Tight.countable_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:50:33.475381+00:00
-- url     : https://prove2.me/theorems/18fe70d1-c949-467d-8e48-2b30773fe25d
-- title:
--   Proof of Theorem 5.8, pp. 30–31 — countable-class lower bound
-- statement:
--   Let $\mathcal C$ be a nonempty countable set of strictly positive, nondecreasing cost functions. The worst pure price of anarchy among congestion games using costs from $\mathcal C$ is at least the resourcewise smoothness value:
--
--   $$\gamma(\mathcal C)\le\sup_{G\in\mathcal G(\mathcal C)}\rho_{\mathrm{pure}}(G).$$
--
--   This packages the countable part of the proof of Theorem 5.8, including cases where either side is infinite.
--
--   **Formalization Note** The set is countable but need not be finite. The statement does not impose a bound on player or resource count.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), proof of Theorem 5.8, steps 1–6, pp. 30–31

import Definitions.Def_RobustPoA_Tight_Classes

namespace RobustPoA.Tight

open scoped ENNReal

/-- Proof of Theorem 5.8, steps 1–6, pp. 30–31: the lower bound for a countable
class of strictly positive cost functions. -/
theorem countable_case (C : Set (ℕ → ℝ)) (hcount : C.Countable)
    (hne : C.Nonempty) (hC : ∀ c ∈ C, IsCostFn c ∧ IsStrictlyPos c) :
    gamma C ≤ worstPoA C := by sorry

end RobustPoA.Tight
