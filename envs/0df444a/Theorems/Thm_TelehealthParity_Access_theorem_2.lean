-- Prove2me | Theorems.Thm_TelehealthParity_Access_theorem_2
-- name    : TelehealthParity.Access.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:56.149643+00:00
-- url     : https://prove2.me/theorems/679dda79-3b2f-4870-b696-00a4a944574e
-- title:
--   Theorem 2 — BO is an equilibrium iff $\theta\in[0,\theta^T]$
-- statement:
--   Under the standing assumptions, let $q$ be admissible. For every telehealth commitment $\theta\in[0,1]$, there is an equilibrium in which patients mix between balking and the office only ($\pi^B>0$, $\pi^O>0$, $\pi^T=0$) if and only if
--   $$\theta\in[0,\theta^T].$$
--
--   For small telehealth commitments telehealth is too congested to be used, and the office channel alone serves patients.
--
--   **Formalization Note** At $\theta=0$ the telehealth queue has no capacity; it is then unavailable and imposes no constraint (definition `TelehealthParity.Access.Equilibrium`).
-- source:
--   Çakıcı and Mills, Telehealth in Acute Care: Pay Parity and Patient Access, SSRN working paper (version of August 19, 2024), p. 14, Theorem 2; proof Appendix C, EC p. 5 (PDF 38)

import Mathlib
import Definitions.Def_TelehealthParity_Access_Setting
import Definitions.Def_TelehealthParity_Access_Equilibrium

namespace TelehealthParity.Access

theorem theorem_2 (p : Params) (hp : p.Standing) (q : ℝ) (hq : Admissible p q)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    IsBO p q θ ↔ θ ∈ Set.Icc 0 (thetaT p q) := by sorry

end TelehealthParity.Access
