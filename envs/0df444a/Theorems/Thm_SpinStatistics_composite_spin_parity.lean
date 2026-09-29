-- Prove2me | Theorems.Thm_SpinStatistics_composite_spin_parity
-- name    : SpinStatistics.composite_spin_parity
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:07:02.99899+00:00
-- url     : https://prove2.me/theorems/f2947727-af06-4426-9f2f-52207d957ed2
-- title:
--   Addition of angular momenta: total spin is integer iff the number of half-integer constituents is even
-- statement:
--   Record spins in units of $\hbar/2$, so a spin $j$ is the natural number $2j$. Let $l=(a_1,\dots,a_m)$ be the doubled spins of the constituents of a composite particle and let $J$ be a doubled total spin obtainable from them by the quantum-mechanical addition of angular momenta (repeated Clebsch–Gordan coupling: coupling doubled spins $a$ and $b$ gives exactly the $J$ with $|a-b|\le J\le a+b$, $J\equiv a+b\pmod 2$). Then
--   $$J\equiv \#\{\,r : a_r \text{ odd}\,\}\pmod 2 .$$
--   Equivalently, the composite has integer spin iff it contains an even number of half-integer-spin constituents, and half-integer spin iff that number is odd.
-- source:
--   Wikipedia, "Spin–statistics theorem" (https://en.wikipedia.org/wiki/Spin%E2%80%93statistics_theorem), PDF snapshot supplied by the proposal owner; section 'Composite particles', p. 4, first paragraph (sentence 4)

import Mathlib
import Definitions.Def_SpinStatistics_Defs

namespace SpinStatistics

theorem composite_spin_parity (l : List ℕ) (J : ℕ) (h : CanAddTo l J) :
    J % 2 = (l.countP (fun a => a % 2 = 1)) % 2 := by sorry

end SpinStatistics
