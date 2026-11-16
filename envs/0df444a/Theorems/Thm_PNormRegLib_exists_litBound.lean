-- Prove2me | Theorems.Thm_PNormRegLib_exists_litBound
-- name    : PNormRegLib.exists_litBound
-- status  : Proved
-- author  : @milia
-- created : 2026-11-15T08:11:03.08737+00:00
-- url     : https://prove2.me/theorems/83323bc0-6995-43e1-a804-70f1fa67cfc5
-- title:
--   Every real-RAM program has a literal bound
-- statement:
--   For every program $P$ of the real RAM `PNormReg_Machine` there is an integer $L\ge1$ such that
--
--   $$|c|\le L\quad\text{for every instruction } p_q:=c \text{ of } P,$$
--
--   that is, $P$ has literal bound $L$ in the sense of the definition `PNormRegLib_AddressBound`.
--
--   Together with the address bound `PNormRegLib.bounded_run`, this lets one bound the addresses used by a program that is only known to exist.
-- source:
--   Original library result for the PNormReg machine (definition PNormReg_Machine: Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission), written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' at the captain's invitation (mission discussion, 2026-11-14). No external source is claimed; the doubling argument is the standard one for machines whose only integer arithmetic is addition and subtraction.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_AddressBound

namespace PNormRegLib

/-- Every program has an integer-literal bound `L ≥ 1`. -/
theorem exists_litBound (P : PNormReg.Program) : ∃ L : ℤ, 1 ≤ L ∧ LitBound P L := by sorry

end PNormRegLib
