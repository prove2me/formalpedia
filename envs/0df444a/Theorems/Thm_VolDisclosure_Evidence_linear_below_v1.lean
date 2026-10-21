-- Prove2me | Theorems.Thm_VolDisclosure_Evidence_linear_below_v1
-- name    : VolDisclosure.Evidence.linear_below_v1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:09.697175+00:00
-- url     : https://prove2.me/theorems/6eb41e85-6472-4afb-b625-cf434cff9c12
-- title:
--   Proposition 3's remark, p. 19 — firm value is linear on [0, v^1]
-- statement:
--   Fix parameters satisfying the standing assumptions of §3, an evidence probability $\pi \in [0,1)$, and let $s$ be the firm value. Below the first termination threshold $v^1 = v^1(\pi)$ firm value is linear through the origin:
--   $$
--   s(v) = \frac{v}{v^1}\, s(v^1) \qquad \text{for all } v \in [0, v^1].
--   $$
--
--   The paper states this after Proposition 3 ("In addition, firm value in this region is linear") and uses it in the proof of Proposition 4(a) (p. 41). Because $v^1$ moves with $\pi$, it is also what shows that the strict comparative static of Proposition 4(a) can fail below $v^1$.
--
--   **Formalization Note.** The value at $v = 0$ is $0$ (termination is certain there); the statement includes the endpoints $0$ and $v^1$.
-- source:
--   Fu & Trigilia, Voluntary Disclosure, Moral Hazard and Default Risk, working paper (August 28, 2019), p. 19, remark after Proposition 3 ("In addition, firm value in this region is linear."); used p. 41, proof of Proposition 4(a)

import Mathlib
import Definitions.Def_VolDisclosure_Evidence_Model

namespace VolDisclosure.Evidence

/-- Proposition 3's remark (p. 19), used on p. 41: firm value is linear on `[0, v¹]`. -/
theorem linear_below_v1 (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π < 1)
    (s : ℝ → ℝ) (hs : IsValue P π s) :
    ∀ v, 0 ≤ v → v ≤ P.v1 π → s v = v / P.v1 π * s (P.v1 π) := by sorry

end VolDisclosure.Evidence
