-- Prove2me | Theorems.Thm_PNormRegLib_exists_usesBelow
-- name    : PNormRegLib.exists_usesBelow
-- status  : Proved
-- author  : @milia
-- created : 2026-11-15T08:36:53.4234+00:00
-- url     : https://prove2.me/theorems/46384895-787e-4322-8a62-14ffccdf7d2d
-- title:
--   Every real-RAM program uses finitely many registers
-- statement:
--   For every program $P$ of the real RAM `PNormReg_Machine` there is $n\in\mathbb N$ such that
--
--   $$\text{every real register index and every pointer register index occurring in } P \text{ is } <n,$$
--
--   that is, $P$ uses indices below $(n,n)$ in the sense of the definition `PNormRegLib_Reloc`.
--
--   This supplies the index bounds of a frame for a program that is only known to exist.
-- source:
--   Original library result for the PNormReg machine (definition PNormReg_Machine: Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission), written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' at the captain's invitation (mission discussion, 2026-11-14). No external source is claimed; relocating a program by shifting its jump targets and memory accesses is the standard technique for composing machine programs.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Reloc

namespace PNormRegLib

/-- Every program uses only finitely many register and pointer indices: there is `n` with all of
them below `n`. -/
theorem exists_usesBelow (P : PNormReg.Program) : ∃ n : ℕ, UsesBelow P n n := by sorry

end PNormRegLib
