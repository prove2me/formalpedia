-- Prove2me | Theorems.Thm_SennottDP_BOR_sen12_of_standard
-- name    : SennottDP.BOR.sen12_of_standard
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T11:30:07.761613+00:00
-- url     : https://prove2.me/theorems/e405b32a-a24b-44da-bf8b-b8c03eebbdd3
-- title:
--   Proposition 7.5.3 — a $z$ standard policy gives (SEN1–2)
-- statement:
--   If there exists a $z$ standard (randomized stationary) policy $d$, then (SEN1) and (SEN2) hold for the distinguished state $z$: $(1-\alpha)V_\alpha(z)$ is bounded for $\alpha\in(0,1)$, and there is a nonnegative finite function $M$ with $V_\alpha(i)-V_\alpha(z)\le M(i)$ for all $i$ and $\alpha\in(0,1)$.
--
--   This is the book's standard method for verifying (SEN1–2).
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 143, Proposition 7.5.3

import Mathlib
import Definitions.Def_SennottDP_BOR_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.BOR

/-- Sennott (1999), Proposition 7.5.3, p. 143. If there exists a `z` standard (randomized
stationary) policy `d`, then (SEN1) and (SEN2) hold for `z`. -/
theorem sen12_of_standard {S Act : Type} [Countable S] (M : SennottDP.Discounted.MDC S Act) (z : S)
    (hd : ∃ d : RandStationaryPolicy M, IsZStandard d.toPolicy z) :
    SEN1 M z ∧ ∃ Mf : S → ℝ, SEN2 M z Mf := by sorry

end SennottDP.BOR
