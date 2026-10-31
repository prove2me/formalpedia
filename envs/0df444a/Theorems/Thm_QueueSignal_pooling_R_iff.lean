-- Prove2me | Theorems.Thm_QueueSignal_pooling_R_iff
-- name    : QueueSignal.pooling_R_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:06:39.871775+00:00
-- url     : https://prove2.me/theorems/b4bedc52-572f-4642-987d-3962f341fc10
-- title:
--   §4.2 item (1) — $(R,R)$ is a sequential equilibrium with $\delta^R=\delta$ and off-path $\delta^C$ iff $\lambda^U(\delta^C)\le\lambda^O(\delta)$
-- statement:
--   Consider the queue-disclosure game with only uninformed customers, $\mu,\theta>0$, $V_H>V_L>\theta/\mu$, $0<\delta<1$, and a potential arrival rate $\lambda>0$. For the pooling profile $(R,R)$, in which both types reveal the queue:
--
--   1. in every pure sequential equilibrium on $(R,R)$, the belief after $R$ is the prior, $\delta^R=\delta$;
--   2. for every off-path belief $\delta^C\in[0,1]$, the profile $(R,R)$ with beliefs $\delta^R=\delta$ and $\delta^C$ is a pure sequential equilibrium if and only if
--   $$\lambda^U(\delta^C)\le\lambda^O(\delta).$$
--
--   So the sequential equilibrium concept alone allows pooling on revelation for any off-path belief that makes concealing unattractive.
--
--   Differences from the source:
--   - encoding: server and customers play the full signaling game; sequential rationality of the customers (Naor's threshold n(δ^R) in the revealed queue, the joining probability p(δ^C) of (2) in the concealed queue) → the server's payoff after R under belief d is λ^O(d) of (1), after C it is λ^U(d) of (3), the same for both types; reason: the paper's own reduction on p.548 (sequential rationality is equivalent to the customers playing (n(δ^R), p(δ^C)) and the server maximizing its effective arrival rate; π_{i,H} = π_{i,L})
--   - encoding: beliefs δ^R, δ^C → real numbers in [0, 1], one per signal (a function Sig → ℝ); reason: Lean convention; same instances
--   - generalization: "As long as the off-equilibrium-path belief δ^C satisfies λ^U(δ^C) ≤ λ^O(δ), both types have no incentive to deviate" (the if direction) → an iff; reason: the converse is the best-response condition itself; the iff implies the printed statement
-- source:
--   Guo, Haviv, Luo, Wang, Signaling Service Quality Through Queue Disclosure, MSOM 25(2) (2023), doi:10.1287/msom.2022.1170, §4.2, item (1), p.549

import Mathlib
import Definitions.Def_QueueSignal_SignalingGame
import Definitions.Def_QueueSignal_QueueModel

namespace QueueSignal

/-- **Pooling on `R`** (Guo, Haviv, Luo, Wang, *Signaling Service Quality Through Queue Disclosure*, MSOM 25(2) (2023),
doi:10.1287/msom.2022.1170, §4.2, item (1), p.549, PDF p.8).

In the baseline game (all customers uninformed), in every pure sequential equilibrium on the
profile `(R, R)` the belief after `R` is the prior, `δ^R = δ`; and for every off-path belief
`δ^C ∈ [0, 1]`, the profile `(R, R)` with beliefs `δ^R = δ`, `δ^C` is a pure sequential
equilibrium if and only if `λ^U(δ^C) ≤ λ^O(δ)`. -/
theorem pooling_R_iff (P : Params) (hP : P.Valid) (lam : ℝ) (hlam : 0 < lam) :
    (∀ b : Sig → ℝ, IsPureSE P.δ (pay P lam) (.R, .R) b → b .R = P.δ) ∧
    ∀ dC : ℝ, 0 ≤ dC → dC ≤ 1 →
      (IsPureSE P.δ (pay P lam) (.R, .R) (beliefs P.δ dC) ↔ lamU P lam dC ≤ lamO P lam P.δ) := by sorry

end QueueSignal
