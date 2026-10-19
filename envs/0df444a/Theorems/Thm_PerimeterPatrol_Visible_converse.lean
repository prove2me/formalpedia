-- Prove2me | Theorems.Thm_PerimeterPatrol_Visible_converse
-- name    : PerimeterPatrol.Visible.converse
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:23:53.118022+00:00
-- url     : https://prove2.me/theorems/6fe4e925-fa24-44c8-8efb-6c8e58715e9b
-- title:
--   Theorem 2, proof, pp. 7–8 — no feasible strategy guarantees more than V(λ, t, p): some fixed attack time comes within ε
-- statement:
--   Let $\lambda > 0$, $t > 0$, $p \in (0, 1]$, and let $\mu$ be any feasible mixed strategy of the defender (a probability measure on dispatch sequences, almost surely satisfying condition (1) with rate $\lambda$). For every $\varepsilon > 0$ there is a start time $y > 0$ such that the attack that starts at the fixed time $y$ (and occupies $(y, y + t]$) is detected with probability
--
--   $$P_{\mathrm{det}}(\mu, y) < V(\lambda, t, p) + \varepsilon .$$
--
--   So no feasible patrol strategy can guarantee more than the value (2), even against an attacker who ignores what he sees. Together with the guarantee of the blue–red schedule this identifies (2) as the value of the game.
--
--   **Formalization Note.** The attack here is deterministic (a constant start time with operating window $[y, y + t]$), which is a special case of an adaptive attack, so this statement is at least as strong as "there is an attack". The paper's sentence "she needs to increase $E[N]$" is not used as a hypothesis or conclusion: a feasible mixed strategy can have infinite expected count in every window while each path has rate $\lambda$, so the statement is about the detection probability itself.
-- source:
--   Lin, Optimal Patrol of a Perimeter, arXiv:1905.03600v3, pp. 7–8, Theorem 2, proof, second paragraph

import Mathlib
import Definitions.Def_PerimeterPatrol_Visible_Model

open MeasureTheory

namespace PerimeterPatrol.Visible
theorem converse (lam t p : ℝ) (hlam : 0 < lam) (ht : 0 < t) (hp0 : 0 < p) (hp1 : p ≤ 1) (μ : Measure (ℕ → ℝ)) (hμ : IsMixedStrategy lam μ) (ε : ℝ) (hε : 0 < ε) : ∃ y : ℝ, 0 < y ∧ detectionProb p t μ (fun _ => y) < patrolValue lam t p + ε := by sorry
end PerimeterPatrol.Visible
