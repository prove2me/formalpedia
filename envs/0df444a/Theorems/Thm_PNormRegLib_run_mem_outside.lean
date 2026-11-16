-- Prove2me | Theorems.Thm_PNormRegLib_run_mem_outside
-- name    : PNormRegLib.run_mem_outside
-- status  : Proved
-- author  : @milia
-- created : 2026-11-15T08:11:02.916232+00:00
-- url     : https://prove2.me/theorems/137e1e42-db4c-4591-b90d-5d7443aed320
-- title:
--   Locality of real-RAM runs
-- statement:
--   Let $P$ be a program of the real RAM `PNormReg_Machine`, let $\omega$ be a coin tape, let $X\ge1$ be an integer, and let $s$ be an $X$-bounded state (definition `PNormRegLib_AddressBound`) such that $X$ is also a literal bound for $P$. Write $s_t$ for the state after $t$ steps of $P$ from $s$ on $\omega$. Then for every $t\in\mathbb N$ and every address $y\in\mathbb Z$ with $|y|>X\cdot2^t$,
--
--   $$M_{s_t}(y)=M_s(y)\qquad\text{and}\qquad I_{s_t}(y)=I_s(y),$$
--
--   where $M$ is the real memory and $I$ the integer memory.
--
--   A run of $t$ steps therefore leaves all memory outside the window $[-X2^t,X2^t]$ untouched, which is the frame property needed to compose programs.
-- source:
--   Original library result for the PNormReg machine (definition PNormReg_Machine: Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission), written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' at the captain's invitation (mission discussion, 2026-11-14). No external source is claimed; the doubling argument is the standard one for machines whose only integer arithmetic is addition and subtraction.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_AddressBound

namespace PNormRegLib

open PNormReg

/-- **Locality.** Under the hypotheses of `bounded_run`, a run of `t` steps leaves every real and
every integer memory cell at an address `y` with `|y| > X · 2^t` unchanged. -/
theorem run_mem_outside (P : Program) (ω : ℕ → Bool) (X : ℤ) (s : State) (hs : PBounded X s)
    (hlit : LitBound P X) (hX : 1 ≤ X) (t : ℕ) (y : ℤ) (hy : X * 2 ^ t < |y|) :
    (run P s ω t).core.mem y = s.core.mem y ∧
      (run P s ω t).integerMemory y = s.integerMemory y := by sorry

end PNormRegLib
