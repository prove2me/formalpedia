-- Prove2me | Theorems.Thm_SensitivityStrictGateStates_strict_guard_conditions_iff
-- name    : SensitivityStrictGateStates.strict_guard_conditions_iff
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:50:39.24607+00:00
-- url     : https://prove2.me/theorems/e9abb686-50b8-4bcd-b177-d2fb742d1be2
-- title:
--   Strict guard legality is equivalent to weighted count at most one
-- statement:
--   Let a nested family be used in a strict recipe of either form: zero soft allowance with disabled hard cutoff, or soft allowance one with an enabled hard cutoff at least the soft cutoff. Put $e=\mathrm{hard}$ when enabled and $e=\mathrm{soft}$ otherwise, and define
--   $$
--   w_j(h)=\mathbf1_{\mathrm{soft}(j)<h}+\mathbf1_{e(j)<h}.
--   $$
--   The soft-count and hard-quietness conditions hold exactly when
--   $$
--   \sum_{Q\in\mathcal G(v)}w_j(h_Q)\le1.
--   $$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/StrictGateStates.lean lines 70–94; SHA256 8a707cceb665a7f88c56310be7495b8933682225933379f4c87f2becce290cbf; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_StrictGateStates
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityFiniteRanks
end SensitivityFiniteRanks
namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivityStrictGateStates
end SensitivityStrictGateStates
namespace SensitivityTargetEvents
end SensitivityTargetEvents


/-!
Exact finite-state semantics for the strict rows in the P/J recurrences.
Ordinary strict rows have zero tolerance and a disabled hard cutoff; warm
strict rows have allowance one and a finite hard cutoff. Both are represented
by the source's sum of two indicator weights, with legal total at most one.
-/
open SensitivityStrictGateStates
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityProfile456 SensitivityGuardEvents
open SensitivityFiniteRanks SensitivityTargetEvents
set_option autoImplicit false
variable {I Color V S : Type} {L : ℕ}

theorem SensitivityStrictGateStates.strict_guard_conditions_iff {row : RowFamily I Color L} (hnested : Nested row)
    (guards : GuardFamily V S) (recipe : GateRecipe S L) (v : V) (j : Fin L)
    (hshape : StrictGuardShape recipe j) (x : ((V × S) × I) → Bool) :
    (guardCount row guards v (recipe.soft j) x ≤ recipe.allowance j ∧
      ∀ check ∈ guards v, ¬ guardActive row (recipe.hard j) x check) ↔
    weightCount row guards recipe v j x ≤ 1 := by sorry
