-- Prove2me | Theorems.Thm_SensitivityBaselineLossNumeric_dual_total_bound
-- name    : SensitivityBaselineLossNumeric.dual_total_bound
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:48:44.050177+00:00
-- url     : https://prove2.me/theorems/07aebaf9-15d8-482c-a5f0-578c1eb6da0c
-- title:
--   Soundness of the baseline loss dual certificate
-- statement:
--   Let a finite collection of checks realize the size and occupancy totals of a numerical state $s$. Assume every check is an allowed column, the total socket count and check count equal the recipe parameters, the weak and strong occupancy sums equal the two recorded failure counts, and the extra occupancy sum is at least the selected branch requirement. For any valid dual certificate,
--   $$
--   \operatorname{ownFee}(s)+\sum_{Q}|Q|\,\operatorname{guardFee}(s,h_Q)\le M'_{ij}.
--   $$
--   All quantities in this inequality are natural-number fees from the fixed input and output profiles.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/BaselineLossDualSoundness.lean lines 14–68; SHA256 0c45937d5a5bb6e3af6f8250b6dd6cbfed0c29d3092abd9f689d5c41500c9129; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossNumeric
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityBaselineLossNumeric
end SensitivityBaselineLossNumeric


/-! Exact soundness of the five-statistic integer dual certificates. -/
open SensitivityBaselineLossNumeric
open scoped BigOperators

theorem SensitivityBaselineLossNumeric.dual_total_bound {T : Type} (checks : Finset T)
    (r : Recipe) (input output : Array ℕ) (i j : Fin 12) (s : State)
    (branch : Fin 2) (cert : Dual) (hcert : Valid r input output i j s branch cert)
    (height : T → Fin 13) (size : T → Fin 3)
    (hallowed : ∀ t ∈ checks, AllowedColumn r i j s (height t) (size t))
    (hdegree : ∑ t ∈ checks, (size t).val = r.degree)
    (hchecks : checks.card = r.checks)
    (hweak : ∑ t ∈ checks, occupied (r.soft i) (height t).val = s.fi.val)
    (hstrong : ∑ t ∈ checks, occupied (r.soft j) (height t).val = s.fj.val)
    (hextra : extraRequired r j s branch ≤
      ∑ t ∈ checks, occupied (extraCut r j branch) (height t).val) :
    ownFee r input i s + ∑ t ∈ checks, (size t).val * guardFee r input i s (height t).val ≤
      SensitivityLocalNumeric.entry output 2 i.val j.val := by sorry
