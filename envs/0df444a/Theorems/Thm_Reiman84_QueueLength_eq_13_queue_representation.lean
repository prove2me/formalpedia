-- Prove2me | Theorems.Thm_Reiman84_QueueLength_eq_13_queue_representation
-- name    : Reiman84.QueueLength.eq_13_queue_representation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:48:31.03489+00:00
-- url     : https://prove2.me/theorems/b5d5f6cf-6953-44ee-ad9f-69841494b56d
-- title:
--   Eq. (13) — Q(t) = X̃(t) + Y(t)(I − P)
-- statement:
--   Let $(Q,B)$ solve (1)–(3) for one network of §2 at a sample point, with idleness $I_k(t)=t-B_k(t)$ and $Y_k(t)=\mu_kI_k(t)$. Then for every $t\ge0$
--   $$Q_k(t)=\tilde X_k(t)+Y_k(t)-\sum_{i=1}^Kp_{ik}Y_i(t),\qquad 1\le k\le K,$$
--   that is,
--   $$Q(t)=\tilde X(t)+Y(t)(I-P).$$
--
--   This identity expresses the queue length as the image of the centred process $\tilde X$ under the map $f$ of Proposition 2, which is how the limit theorem is reduced to a limit theorem for $\tilde X$.
-- source:
--   Reiman, Open Queueing Networks in Heavy Traffic, Math. Oper. Res. 9(3) (1984), p. 444, Eqs. (12)–(13)

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Network

namespace Reiman84.QueueLength

open MeasureTheory

/-- Eq. (13), p. 444: every solution `(Q, B)` of (1)–(3) satisfies
`Q(t) = X̃(t) + Y(t)(I − P)` for `t ≥ 0`, where `Y_k(t) = μ_k I_k(t)`. -/
theorem eq_13_queue_representation {K : ℕ} {J : Finset (Fin K)} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (N : Network K J P) (ω : Ω)
    (Q B : ℝ → Fin K → ℝ) (h : N.IsQueueSolution ω Q B) :
    ∀ t, 0 ≤ t → Q t = N.Xtilde B t ω + Matrix.vecMul (N.Y B t) (1 - N.routing) := by sorry

end Reiman84.QueueLength
