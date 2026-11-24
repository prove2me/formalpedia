-- Prove2me | Theorems.Thm_SensitivityLocalNumeric_mem_localStates
-- name    : SensitivityLocalNumeric.mem_localStates
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:50:31.49608+00:00
-- url     : https://prove2.me/theorems/355613df-c9b7-4c25-b118-ae9d72f06852
-- title:
--   Exact characterization of the enumerated local states
-- statement:
--   A state $s=(a,b,\mathbf h)$ belongs to the finite local-state list for recipe $r$ and target rank $n$ exactly when
--   $$
--   6\le a,b\le12,\qquad |\mathbf h|\le2,\qquad
--   \mathrm{soft}_r(n)<h\le12\ \text{for every }h\in\mathbf h,
--   $$
--   and, when $r$ is unary, $a=b$. Thus enumeration is equivalent to the stated admissibility predicate.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/LocalNumericRecurrence.lean lines 117–150; SHA256 a5770df37a51e23b906cd6cee034e85040644f7b9889626f6cdd7427ad34764c; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range

namespace SensitivityLocalNumeric
end SensitivityLocalNumeric


/-!
Finite local recurrence evaluator at the exact literal profiles. Heights are
one greater than the source's exact ranks, with zero denoting no accepted rank.
All ordered target pairs and all guard lists of length at most two are covered.
These definitions describe numeric certificates; semantic cost soundness is
provided separately by the event-set lemmas.
-/
open SensitivityLocalNumeric

theorem SensitivityLocalNumeric.mem_localStates (r : Recipe) (n : Fin 12) (s : State) :
    s ∈ localStates r n ↔ AdmissibleState r n s := by sorry
