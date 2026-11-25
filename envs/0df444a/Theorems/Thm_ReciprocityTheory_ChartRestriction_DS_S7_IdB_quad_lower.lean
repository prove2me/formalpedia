-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_IdB_quad_lower
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.IdB.quad_lower
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:44:16.348156+00:00
-- url     : https://prove2.me/theorems/3c0f30f9-7c91-403e-a774-334c53cd35b4
-- title:
--   Id B: quad lower
-- statement:
--   The Id B construction uses the quad lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/IdThmB.lean#L46-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/IdThmB.lean#L46-L85

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IdThmB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.IdB

theorem ReciprocityTheory.ChartRestriction.DS.S7.IdB.quad_lower {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    ∃ c > 0, ∀ v : Fin n → ℂ, c * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ (x *ᵥ v)).re := by sorry
