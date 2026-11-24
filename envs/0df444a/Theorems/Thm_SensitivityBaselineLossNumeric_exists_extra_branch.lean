-- Prove2me | Theorems.Thm_SensitivityBaselineLossNumeric_exists_extra_branch
-- name    : SensitivityBaselineLossNumeric.exists_extra_branch
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:48:46.230311+00:00
-- url     : https://prove2.me/theorems/e1ec1661-69cb-47b6-887c-b4439cc1287a
-- title:
--   A rejection witness at the next rank
-- statement:
--   Let a numerical recipe have target ranks monotone in the failure count. Suppose the fixed child ranks and actual guard-count function reject the rank immediately above $j$, whenever $j<11$. Then there is a branch $b\in\{0,1\}$ such that
--   $$
--   \operatorname{extraRequired}(r,j,s,b)
--   \le C\bigl(\operatorname{extraCut}(r,j,b)\bigr).
--   $$
--   At the top rank $j=11$, branch zero is chosen. Below the top rank, the two branches correspond to sufficient soft failures or a positive hard-guard count.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/BaselineNumericProperties.lean lines 41–59; SHA256 20b62da10ce872e52f749fd179607f55d40ba042872fd18601f489156a844cf8; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossNumeric
import Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineNumericProperties
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.List.Range

namespace SensitivityBaselineLossNumeric
end SensitivityBaselineLossNumeric


/-! Mathematical coverage facts for the baseline loss certificate states. -/
open SensitivityBaselineLossNumeric

theorem SensitivityBaselineLossNumeric.exists_extra_branch (r : Recipe) (hmono : TargetMonotone r)
    (j : Fin 12) (s : State) (counts : ℕ → ℕ)
    (hreject : j.val < 11 → ¬ accepts r (nextRank j)
      (counts (r.soft (nextRank j))) (counts (r.hard (nextRank j))) s.a.val s.b.val) :
    ∃ branch : Fin 2, (j.val = 11 → branch.val = 0) ∧
      extraRequired r j s branch ≤ counts (extraCut r j branch) := by sorry
