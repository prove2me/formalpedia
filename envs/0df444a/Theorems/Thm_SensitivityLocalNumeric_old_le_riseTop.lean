-- Prove2me | Theorems.Thm_SensitivityLocalNumeric_old_le_riseTop
-- name    : SensitivityLocalNumeric.old_le_riseTop
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:50:32.320718+00:00
-- url     : https://prove2.me/theorems/3e53303f-6d61-4708-82f0-dc87ddc09121
-- title:
--   The searched upward cutoff never precedes the old height
-- statement:
--   For any numerical recipe, rank, residual count, and local state, if the upward cutoff search returns an actual rank below $12$, then
--   $$
--   \operatorname{riseTop}(r,c,\mathrm{rest},s,h)<12
--   \quad\Longrightarrow\quad
--   h\le\operatorname{riseTop}(r,c,\mathrm{rest},s,h).
--   $$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/LocalNumericRecurrence.lean lines 197–209; SHA256 a5770df37a51e23b906cd6cee034e85040644f7b9889626f6cdd7427ad34764c; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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

theorem SensitivityLocalNumeric.old_le_riseTop (r : Recipe) (c : Fin 12) (rest : ℕ) (s : State) (old : ℕ)
    (htop : riseTop r c rest s old < 12) : old ≤ riseTop r c rest s old := by sorry
