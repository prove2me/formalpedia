-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_paU_pt
-- name    : ReciprocityTheory.ChartRestriction.G.I2.FPw.paU_pt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:24.322453+00:00
-- url     : https://prove2.me/theorems/1dbc5c1b-5bac-443c-b072-ad98f555d388
-- title:
--   FPw: pa U pt
-- statement:
--   The FPw construction uses the pa U pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/DetMEq.lean#L48-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/DetMEq.lean#L48-L85

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfNegRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_DetMEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical

theorem ReciprocityTheory.ChartRestriction.G.I2.FPw.paU_pt {q c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a v : EuclideanSpace ℂ ι, ‖paU q a F v‖ ≤
      C * (1 + ‖v‖) ^ c * Real.exp ((q * Real.pi) * ‖v‖ ^ 2) *
        ((1 + ‖a‖) ^ (2 * c) * Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 4)) := by sorry
