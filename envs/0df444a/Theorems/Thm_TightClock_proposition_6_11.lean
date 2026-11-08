-- Prove2me | Theorems.Thm_TightClock_proposition_6_11
-- name    : TightClock.proposition_6_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:29:03.182564+00:00
-- url     : https://prove2.me/theorems/7a44e8f8-21d4-4470-8a57-f9e8eaea3e3f
-- title:
--   Proposition 6.11 — clock bound
-- statement:
--   On a good tree, every randomized clock auction has expected welfare at most
--
--   $$\frac{(e^a-1+a^2)B+3}{a(1-a)}.$$
--
--   For fixed $q$ and large $L$, every clock auction thus obtains about one portion of welfare, whereas the optimum obtains $L$ portions.
--
--   **Formalization Note** This is stated for the clock class of §3 and §6.1 and not for single-step clocks: the reduction of §6.2 is part of the proof.
--
--   Differences from the source:
--   - encoding: the depth $L$ of the tree, with levels $r=1,\dots,L$ in Instance 11 → the hypothesis `1 ≤ L`; reason: at $L=0$ there are no bidders and $h=a^2B/L$ divides by zero; the page's construction has $L\ge1$
--   - generalization: the clock of §3, which serves its whole active set when that set terminates the auction → the wider class of §6.1, in which offers may continue after feasibility and any feasible subset of the active set may be served; prices are arbitrary nonnegative reals and rounds are unbounded; reason: p.34 widens the class for this upper bound; a bound over the wider class implies it for the §3 clocks, which are members
--   - encoding: a clock has a measurable public seed, with payments → seed space in `Type`, welfare at each nonnegative profile measurable in the seed, no payments, and welfare $0$ on a non-terminating run; reason: p.14 evaluates clocks only through welfare and gives non-terminating runs no service; the measurability makes the expectation meaningful
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Proposition 6.11, §6.6, p.47 (PDF p.50)

import Mathlib
import Definitions.Def_TightClock_clockValue
import Definitions.Def_TightClock_familyOf
import Definitions.Def_TightClock_hardPrior
import Definitions.Def_TightClock_IsGoodTree

set_option autoImplicit false

namespace TightClock

/-- Proposition 6.11 (Clock bound), p.47 (PDF 50), of Afshinmehr et al., manuscript (STOC 2027 submission): on a good
tree, every randomized clock auction has expected welfare at most `((eᵃ − 1 + a²) B + 3) / (a (1 − a))`.

**Formalization Note** It is stated for the clock class of §3 and §6.1, not for single-step clocks. -/
theorem proposition_6_11 (q L : ℕ) (hq : 8 ≤ q) (hL : 1 ≤ L) (T : Tree q L) (hT : IsGoodTree T)
    (π : RandomizedClock (familyOf T)) :
    clockValue π (hardPrior q L hq hL) ≤
      ((Real.exp (a q) - 1 + (a q) ^ 2) * (B L : ℝ) + 3) / (a q * (1 - a q)) := by sorry

end TightClock
