-- Prove2me | Theorems.Thm_QueueSignal_separating_CR
-- name    : QueueSignal.separating_CR
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:06:39.139248+00:00
-- url     : https://prove2.me/theorems/6dfb36c3-d59c-43e1-9610-cb3791ee8bd9
-- title:
--   §4.2 item (4) — $(C,R)$ is a sequential equilibrium iff $\delta^R=0$, $\delta^C=1$ and $\lambda^O(0)=\lambda^U(1)$
-- statement:
--   Consider the queue-disclosure game with only uninformed customers, $\mu,\theta>0$, $V_H>V_L>\theta/\mu$, $0<\delta<1$, and a potential arrival rate $\lambda>0$. The separating profile $(C,R)$, in which the high-quality server conceals and the low-quality server reveals the queue, is a pure sequential equilibrium with beliefs $(\delta^R,\delta^C)$ if and only if $\delta^R=0$, $\delta^C=1$ and
--   $$\lambda^O(0)=\lambda^U(1).$$
--
--   Differences from the source:
--   - encoding: server and customers play the full signaling game; sequential rationality of the customers (Naor's threshold n(δ^R) in the revealed queue, the joining probability p(δ^C) of (2) in the concealed queue) → the server's payoff after R under belief d is λ^O(d) of (1), after C it is λ^U(d) of (3), the same for both types; reason: the paper's own reduction on p.548 (sequential rationality is equivalent to the customers playing (n(δ^R), p(δ^C)) and the server maximizing its effective arrival rate; π_{i,H} = π_{i,L})
--   - encoding: beliefs δ^R, δ^C → real numbers in [0, 1], one per signal (a function Sig → ℝ); reason: Lean convention; same instances
--   - generalization: "can be sustained only if λ^O(0) = λ^U(1)" (only if) → an iff, with the beliefs δ^R = 0, δ^C = 1; reason: the converse also holds; the iff implies the printed statement
-- source:
--   Guo, Haviv, Luo, Wang, Signaling Service Quality Through Queue Disclosure, MSOM 25(2) (2023), doi:10.1287/msom.2022.1170, §4.2, item (4), p.549

import Mathlib
import Definitions.Def_QueueSignal_SignalingGame
import Definitions.Def_QueueSignal_QueueModel

namespace QueueSignal

/-- **Separation `(C, R)`** (Guo, Haviv, Luo, Wang, *Signaling Service Quality Through Queue Disclosure*, MSOM 25(2) (2023),
doi:10.1287/msom.2022.1170, §4.2, item (4), p.549, PDF p.8).

In the baseline game, the profile `(C, R)` (the high-quality server conceals, the low-quality
server reveals) with beliefs `b` is a pure sequential equilibrium if and only if
`δ^R = 0`, `δ^C = 1` and `λ^O(0) = λ^U(1)`. -/
theorem separating_CR (P : Params) (hP : P.Valid) (lam : ℝ) (hlam : 0 < lam) (b : Sig → ℝ) :
    IsPureSE P.δ (pay P lam) (.C, .R) b ↔
      b .R = 0 ∧ b .C = 1 ∧ lamO P lam 0 = lamU P lam 1 := by sorry

end QueueSignal
