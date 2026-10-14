-- Prove2me | Theorems.Thm_TelehealthParity_Access_theorem_3
-- name    : TelehealthParity.Access.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:47.194989+00:00
-- url     : https://prove2.me/theorems/cacb03c4-9ecc-44ec-aa39-f4cd473390dc
-- title:
--   Theorem 3 — BT is an equilibrium iff $\theta\in[\theta^O,\bar\theta)$; B iff $\theta\in[\bar\theta,1]$
-- statement:
--   Under the standing assumptions, let $q$ be admissible. For every telehealth commitment $\theta\in[0,1]$:
--   1. there is an equilibrium in which patients mix between balking and telehealth only ($\pi^B>0$, $\pi^T>0$, $\pi^O=0$) if and only if $\theta\in[\theta^O,\bar\theta)$;
--   2. all patients balking, $\pi=(1,0,0)$, is an equilibrium if and only if $\theta\in[\bar\theta,1]$.
--
--   $$\text{BT}\iff \theta\in[\theta^O,\bar\theta),\qquad \text{B}\iff\theta\in[\bar\theta,1].$$
--
--   Together with Theorems 1 and 2 this completes the picture of Figure 3: a high telehealth commitment first pushes all first visits to telehealth, and beyond $\bar\theta$ the office is too congested by duplicate visits for anyone to join.
--
--   **Formalization Note** A channel whose queue is unstable is unavailable in the equilibrium predicate; this is what excludes the $(+)$ root of (16), which the paper discards because it does not give a stable telehealth queue, and it makes all-balking an equilibrium at $\theta=1$.
-- source:
--   Çakıcı and Mills, Telehealth in Acute Care: Pay Parity and Patient Access, SSRN working paper (version of August 19, 2024), p. 15, Theorem 3; proof Appendix C, EC p. 5 (PDF 38)

import Mathlib
import Definitions.Def_TelehealthParity_Access_Setting
import Definitions.Def_TelehealthParity_Access_Equilibrium

namespace TelehealthParity.Access

theorem theorem_3 (p : Params) (hp : p.Standing) (q : ℝ) (hq : Admissible p q)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    (IsBT p q θ ↔ θ ∈ Set.Ico (thetaO p q) (thetaBar p q)) ∧
      (IsB p q θ ↔ θ ∈ Set.Icc (thetaBar p q) 1) := by sorry

end TelehealthParity.Access
