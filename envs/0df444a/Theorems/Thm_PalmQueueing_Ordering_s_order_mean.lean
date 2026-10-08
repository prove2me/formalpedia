-- Prove2me | Theorems.Thm_PalmQueueing_Ordering_s_order_mean
-- name    : PalmQueueing.Ordering.s_order_mean
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T04:02:34.397028+00:00
-- url     : https://prove2.me/theorems/391ba23b-08e9-47d5-8e09-d39a8a3d1ff0
-- title:
--   Lemma 4.4.2 — the S-order compares mean cycle lengths
-- statement:
--   **Lemma 4.4.2.** $F^0 \le_{S\text{-}i} \widetilde F^0$ implies
--   $E_{P^0}[T] \le E_{\widetilde P^0}[\widetilde T]$.
--
--   The $S$-orders are built by dividing Palm integrals **by** the mean cycle length, so it is not
--   obvious that they say anything about that mean itself. This lemma says they do in the
--   $\le_{S\text{-}i}$ case: the normalisation does not hide the comparison it normalises by.
--
--   It is the step Property 4.4.6 needs — the diagram placing the $S$-orders among the integral orders
--   of §4.2.1,
--   $$ \le_{I\text{-}i} \Rightarrow \le_{S\text{-}i} \Rightarrow \le_{S\text{-}I\text{-}i^+}, \qquad
--   \le_{I\text{-}i} \Rightarrow \le_i \Rightarrow \le_{I\text{-}i^+} . \tag{4.4.10} $$
--
--   The proof runs through the equivalent form $F_T \le_i \widetilde F_T$, then (4.4.6),
--   $$ \frac{1}{E_{P^0}[T]}\frac{1}{x}\int_0^x (1 - F^0_T(u))du \ge
--   \frac{1}{E_{\widetilde P^0}[\widetilde T]}\frac{1}{x}\int_0^x (1 - \widetilde F^0_T(u))du , $$
--   and lets $x$ tend to zero, using $F^0_T(0) = \widetilde F^0_T(0) = 0$ — which is the support
--   restriction the $S$-order domain carries, and without which the limit is a different number.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 302, Lemma 4.4.2

import Mathlib
import Definitions.Def_PalmQueueing_Ordering_IntegralOrders
import Definitions.Def_PalmQueueing_Ordering_TimeStationary

/-!
# Lemma 4.4.2: the `S`-order compares mean cycle lengths (§4.4, p.302)
-/

namespace PalmQueueing.Ordering

open MeasureTheory

/-- **Lemma 4.4.2** (p.302). `F⁰ ≤_{S-i} F̃⁰` implies `E_{P⁰}[T] ≤ E_{P̃⁰}[T̃]`.

The `S`-orders are built by dividing Palm integrals by the mean cycle length, so it is not obvious
that they say anything about that mean itself. This lemma says they do, in the `≤_{S-i}` case: the
normalisation does not hide the comparison it normalises by.

It is the step Property 4.4.6 needs, the diagram that places the `S`-orders among the integral
orders of §4.2.1:

`≤_{I-i} ⟹ ≤_{S-i} ⟹ ≤_{S-I-i⁺}`, and `≤_{I-i} ⟹ ≤_i ⟹ ≤_{I-i⁺}`.

The proof runs through the equivalent form `F_T ≤_i F̃_T`, then (4.4.6),

`(1/E_{P⁰}[T])(1/x)∫_0^x (1 − F⁰_T(u))du ≥ (1/E_{P̃⁰}[T̃])(1/x)∫_0^x (1 − F̃⁰_T(u))du`,

and lets `x` tend to zero, using `F⁰_T(0) = F̃⁰_T(0) = 0` — which is the support restriction that
`SOrderDomain` carries, and without which the limit is a different number. -/
theorem s_order_mean {n : ℕ} (F0 F0' : Measure (Fin (n + 1) → ℝ))
    (hdom : SOrderDomain F0) (hdom' : SOrderDomain F0')
    (hle : SILe F0 F0') :
    (∫ z, z 0 ∂F0) ≤ ∫ z, z 0 ∂F0' := by sorry

end PalmQueueing.Ordering
