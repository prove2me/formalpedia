-- Prove2me | Theorems.Thm_PNormRegLib_bounded_run
-- name    : PNormRegLib.bounded_run
-- status  : Proved
-- author  : @milia
-- created : 2026-11-15T08:11:02.131987+00:00
-- url     : https://prove2.me/theorems/6cbb8aa0-a9e5-454c-8ec1-ea6b403d1096
-- title:
--   Address bound for the real RAM
-- statement:
--   Let $P$ be a program of the real RAM `PNormReg_Machine`, let $\omega$ be a coin tape, let $X\ge1$ be an integer, and let $s$ be an $X$-bounded state (definition `PNormRegLib_AddressBound`) such that $X$ is also a literal bound for $P$. Write $s_t$ for the state after $t$ steps of $P$ from $s$ on $\omega$. Then for every $t\in\mathbb N$,
--
--   $$s_t \text{ is } X\cdot2^t\text{-bounded:}\qquad |p_q(s_t)|\le X\cdot2^t\ \text{ and }\ |I_{s_t}(z)|\le X\cdot2^t\ \text{ for all } q,z.$$
--
--   Since one step can at most double the largest integer in absolute value, every address a run uses within $t$ steps lies in $[-X2^t,X2^t]$. This explicit window is the basis for running black-box programs side by side in disjoint memory regions.
-- source:
--   Original library result for the PNormReg machine (definition PNormReg_Machine: Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission), written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' at the captain's invitation (mission discussion, 2026-11-14). No external source is claimed; the doubling argument is the standard one for machines whose only integer arithmetic is addition and subtraction.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_AddressBound

namespace PNormRegLib

open PNormReg

/-- **Address bound.** If all pointers and integer cells of `s` are at most `X ≥ 1` in absolute
value, and so is every integer literal of `P`, then after `t` steps they are at most `X · 2^t`. -/
theorem bounded_run (P : Program) (ω : ℕ → Bool) (X : ℤ) (s : State) (hs : PBounded X s)
    (hlit : LitBound P X) (hX : 1 ≤ X) (t : ℕ) : PBounded (X * 2 ^ t) (run P s ω t) := by sorry

end PNormRegLib
