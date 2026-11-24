-- Prove2me | Theorems.Thm_SteinitzExchange_Duality_Supplement_transport_upper_bound
-- name    : SteinitzExchange.Duality.Supplement.transport_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:34:09.353511+00:00
-- url     : https://prove2.me/theorems/043b3d00-b6a1-4605-8af6-27a516a5c2f8
-- title:
--   Theorem 2.3 — transportation upper bound
-- statement:
--   Let $V$ be a finite nonempty set, let $B\subseteq\mathbb Z^V$ be a finite integral base set and suppose $\omega:B\to\mathbb R$ satisfies (EXC). For all $x,y\in B$ the transportation maximum in (2.8) is finite and attained, and
--   $$\omega(y)\le\omega(x)+\widetilde\omega(x,y).$$
--   The attainment clause spells out the maximum and the finiteness assertion immediately preceding the theorem. The bound uses all nonnegative real transportation plans, with the printed surplus and deficit marginals. **Formalization Note.** `transportBound` takes values in `EReal`; its equality to the value of a feasible real plan asserts a finite maximum, preventing an infinite or default value from trivializing the inequality.
--
--   Differences from the source:
--   none
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 281, Theorem 2.3

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_Exchange
import Definitions.Def_SteinitzExchange_Duality_Supplement_Transportation

namespace SteinitzExchange.Duality.Supplement

/-- Theorem 2.3, p. 281, with the finite attained maximum asserted immediately
above it. This is the real transportation problem printed in (2.8). -/
theorem transport_upper_bound {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (hω : SatisfiesEXC B ω) (x y : V → ℤ) (hx : x ∈ B) (hy : y ∈ B) :
    (∃ shipment : transportArcs B x y → ℝ, IsTransport B x y shipment ∧
      transportBound B ω x y = (transportValue B ω x y shipment : EReal)) ∧
    (ω y : EReal) ≤ (ω x : EReal) + transportBound B ω x y := by sorry

end SteinitzExchange.Duality.Supplement
