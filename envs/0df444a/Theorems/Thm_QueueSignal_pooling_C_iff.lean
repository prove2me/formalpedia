-- Prove2me | Theorems.Thm_QueueSignal_pooling_C_iff
-- name    : QueueSignal.pooling_C_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:07:03.046311+00:00
-- url     : https://prove2.me/theorems/b923e2ba-46d3-4adf-8c95-9c94b391d532
-- title:
--   §4.2 item (2) — $(C,C)$ is a sequential equilibrium with $\delta^C=\delta$ and off-path $\delta^R$ iff $\lambda^O(\delta^R)\le\lambda^U(\delta)$
-- statement:
--   Consider the queue-disclosure game with only uninformed customers, $\mu,\theta>0$, $V_H>V_L>\theta/\mu$, $0<\delta<1$, and a potential arrival rate $\lambda>0$. For the pooling profile $(C,C)$, in which both types conceal the queue:
--
--   1. in every pure sequential equilibrium on $(C,C)$, the belief after $C$ is the prior, $\delta^C=\delta$;
--   2. for every off-path belief $\delta^R\in[0,1]$, the profile $(C,C)$ with beliefs $\delta^R$ and $\delta^C=\delta$ is a pure sequential equilibrium if and only if
--   $$\lambda^O(\delta^R)\le\lambda^U(\delta).$$
--
--   Differences from the source:
--   - encoding: server and customers play the full signaling game; sequential rationality of the customers (Naor's threshold n(δ^R) in the revealed queue, the joining probability p(δ^C) of (2) in the concealed queue) → the server's payoff after R under belief d is λ^O(d) of (1), after C it is λ^U(d) of (3), the same for both types; reason: the paper's own reduction on p.548 (sequential rationality is equivalent to the customers playing (n(δ^R), p(δ^C)) and the server maximizing its effective arrival rate; π_{i,H} = π_{i,L})
--   - encoding: beliefs δ^R, δ^C → real numbers in [0, 1], one per signal (a function Sig → ℝ); reason: Lean convention; same instances
--   - generalization: "the profile … with the off-equilibrium-path belief δ^R satisfying λ^O(δ^R) ≤ λ^U(δ) is a pooling equilibrium" (the if direction), with δ^C = δ "similarly" by Bayes' rule → an iff, plus the Bayes clause δ^C = δ for every sequential equilibrium on (C, C); reason: the converse is the best-response condition itself; the statement implies the printed one
-- source:
--   Guo, Haviv, Luo, Wang, Signaling Service Quality Through Queue Disclosure, MSOM 25(2) (2023), doi:10.1287/msom.2022.1170, §4.2, item (2), p.549

import Mathlib
import Definitions.Def_QueueSignal_SignalingGame
import Definitions.Def_QueueSignal_QueueModel

namespace QueueSignal

/-- **Pooling on `C`** (Guo, Haviv, Luo, Wang, *Signaling Service Quality Through Queue Disclosure*, MSOM 25(2) (2023),
doi:10.1287/msom.2022.1170, §4.2, item (2), p.549, PDF p.8).

In the baseline game, in every pure sequential equilibrium on `(C, C)` the belief after `C` is
the prior, `δ^C = δ`; and for every off-path belief `δ^R ∈ [0, 1]`, the profile `(C, C)` with
beliefs `δ^R`, `δ^C = δ` is a pure sequential equilibrium if and only if
`λ^O(δ^R) ≤ λ^U(δ)`. -/
theorem pooling_C_iff (P : Params) (hP : P.Valid) (lam : ℝ) (hlam : 0 < lam) :
    (∀ b : Sig → ℝ, IsPureSE P.δ (pay P lam) (.C, .C) b → b .C = P.δ) ∧
    ∀ dR : ℝ, 0 ≤ dR → dR ≤ 1 →
      (IsPureSE P.δ (pay P lam) (.C, .C) (beliefs dR P.δ) ↔ lamO P lam dR ≤ lamU P lam P.δ) := by sorry

end QueueSignal
