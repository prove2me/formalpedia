-- Prove2me | Theorems.Thm_RobustPoA_Tight_weak_duality
-- name    : RobustPoA.Tight.weak_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:49:45.108548+00:00
-- url     : https://prove2.me/theorems/f59f497c-d13a-45e9-8faa-2cc0f3e140a7
-- title:
--   §2.4, p. 10 — the pure price of anarchy is at most every valid smoothness ratio
-- statement:
--   Let $G$ be a finite congestion game with a nonnegative social cost on every feasible profile. If $G$ is $(\lambda,\mu)$-smooth and $\mu<1$, then its pure price of anarchy satisfies
--
--   $$\rho_{\mathrm{pure}}(G)\le\frac{\lambda}{1-\mu}.$$
--
--   This is the general upper-bound direction behind tightness: any smoothness certificate limits the cost of every pure Nash equilibrium relative to optimum.
--
--   **Formalization Note** The nonnegative objective is the standing assumption of §2.4. The extended-value convention covers an optimum of zero and games with no pure Nash equilibrium.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), §2.4, p. 10, claim preceding Definition 2.8

import Definitions.Def_RobustPoA_Tight_Classes

namespace RobustPoA.Tight

open scoped ENNReal
open CongestionPoA.AsymSum

/-- §2.4, p. 10: the pure price of anarchy is bounded by any smoothness ratio. -/
theorem weak_duality {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E] (G : CongestionGame ι E)
    (lam mu : ℝ) (hcost : ∀ A, IsProfile G A → 0 ≤ sumCost G A)
    (hsmooth : IsSmoothCG G lam mu) (hmu : mu < 1) :
    purePoA G ≤ ENNReal.ofReal (lam / (1 - mu)) := by sorry

end RobustPoA.Tight
