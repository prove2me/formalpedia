-- Prove2me | Theorems.Thm_TelehealthParity_Access_corollary_2
-- name    : TelehealthParity.Access.corollary_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:09.474177+00:00
-- url     : https://prove2.me/theorems/c6d130a3-a7fc-4d02-a30c-8859b3a4a812
-- title:
--   Corollary 2 — shape of the access rate $A(\theta)$; maximized at $\theta=0$ or $\theta=\theta^*$
-- statement:
--   Under the standing assumptions, let $q$ be admissible. Then the patient access rate $A(\theta)$ of (22)
--   1. is strictly decreasing on $[0,\theta^O)$;
--   2. is concave on $[\theta^O,\bar\theta)$;
--   3. vanishes on $[\bar\theta,1]$;
--   4. attains its maximum over $[0,1]$ at $\theta=0$ or at $\theta=\theta^*$:
--   $$A(\theta)\le A(0)\ \ \forall\theta\in[0,1]\qquad\text{or}\qquad A(\theta)\le A(\theta^*)\ \ \forall\theta\in[0,1].$$
--
--   For patients, as for the provider, only the office-only practice and the telehealth-maximizing commitment are candidates.
--
--   **Formalization Note** The paper's "Assume q > 0" is part of admissibility; $\theta^*$ is the closed form (24).
-- source:
--   Çakıcı and Mills, Telehealth in Acute Care: Pay Parity and Patient Access, SSRN working paper (version of August 19, 2024), p. 17, Corollary 2

import Mathlib
import Definitions.Def_TelehealthParity_Access_Setting

namespace TelehealthParity.Access

theorem corollary_2 (p : Params) (hp : p.Standing) (q : ℝ) (hq : Admissible p q) :
    StrictAntiOn (access p q) (Set.Ico 0 (thetaO p q)) ∧
      ConcaveOn ℝ (Set.Ico (thetaO p q) (thetaBar p q)) (access p q) ∧
      (∀ θ ∈ Set.Icc (thetaBar p q) 1, access p q θ = 0) ∧
      (IsMaxOn (access p q) (Set.Icc 0 1) 0 ∨
        IsMaxOn (access p q) (Set.Icc 0 1) (thetaStar p q)) := by sorry

end TelehealthParity.Access
