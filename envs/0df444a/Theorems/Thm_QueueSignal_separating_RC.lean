-- Prove2me | Theorems.Thm_QueueSignal_separating_RC
-- name    : QueueSignal.separating_RC
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:06:52.766856+00:00
-- url     : https://prove2.me/theorems/5910b665-c77f-4731-b12f-301fc3aebb2b
-- title:
--   §4.2 item (3) — $(R,C)$ is a sequential equilibrium iff $\delta^R=1$, $\delta^C=0$ and $\lambda^O(1)=\lambda^U(0)$
-- statement:
--   Consider the queue-disclosure game with only uninformed customers, $\mu,\theta>0$, $V_H>V_L>\theta/\mu$, $0<\delta<1$, and a potential arrival rate $\lambda>0$. The separating profile $(R,C)$, in which the high-quality server reveals and the low-quality server conceals the queue, is a pure sequential equilibrium with beliefs $(\delta^R,\delta^C)$ if and only if $\delta^R=1$, $\delta^C=0$ and
--   $$\lambda^O(1)=\lambda^U(0).$$
--
--   Separation on $(R,C)$ is therefore possible only at the potential arrival rates where the two equal.
--
--   Differences from the source:
--   - encoding: server and customers play the full signaling game; sequential rationality of the customers (Naor's threshold n(δ^R) in the revealed queue, the joining probability p(δ^C) of (2) in the concealed queue) → the server's payoff after R under belief d is λ^O(d) of (1), after C it is λ^U(d) of (3), the same for both types; reason: the paper's own reduction on p.548 (sequential rationality is equivalent to the customers playing (n(δ^R), p(δ^C)) and the server maximizing its effective arrival rate; π_{i,H} = π_{i,L})
--   - encoding: beliefs δ^R, δ^C → real numbers in [0, 1], one per signal (a function Sig → ℝ); reason: Lean convention; same instances
--   - generalization: "can be sustained only if λ^O(1) = λ^U(0)" (only if) → an iff, with the beliefs δ^R = 1, δ^C = 0; reason: the converse also holds; the iff implies the printed statement
-- source:
--   Guo, Haviv, Luo, Wang, Signaling Service Quality Through Queue Disclosure, MSOM 25(2) (2023), doi:10.1287/msom.2022.1170, §4.2, item (3), p.549

import Mathlib
import Definitions.Def_QueueSignal_SignalingGame
import Definitions.Def_QueueSignal_QueueModel

namespace QueueSignal

/-- **Separation `(R, C)`** (Guo, Haviv, Luo, Wang, *Signaling Service Quality Through Queue Disclosure*, MSOM 25(2) (2023),
doi:10.1287/msom.2022.1170, §4.2, item (3), p.549, PDF p.8).

In the baseline game, the profile `(R, C)` (the high-quality server reveals, the low-quality
server conceals) with beliefs `b` is a pure sequential equilibrium if and only if
`δ^R = 1`, `δ^C = 0` and `λ^O(1) = λ^U(0)`. -/
theorem separating_RC (P : Params) (hP : P.Valid) (lam : ℝ) (hlam : 0 < lam) (b : Sig → ℝ) :
    IsPureSE P.δ (pay P lam) (.R, .C) b ↔
      b .R = 1 ∧ b .C = 0 ∧ lamO P lam 1 = lamU P lam 0 := by sorry

end QueueSignal
