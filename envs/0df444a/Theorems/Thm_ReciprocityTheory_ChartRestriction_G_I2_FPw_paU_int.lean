-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_paU_int
-- name    : ReciprocityTheory.ChartRestriction.G.I2.FPw.paU_int
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:37.16109+00:00
-- url     : https://prove2.me/theorems/c01f9515-9588-4a70-b023-38f2f4aa1e76
-- title:
--   FPw: pa U int
-- statement:
--   The FPw construction uses the pa U int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/PaUContinuous.lean#L65-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/PaUContinuous.lean#L65-L134

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfEqInner
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaUContinuous
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

theorem ReciprocityTheory.ChartRestriction.G.I2.FPw.paU_int {q c : ℕ} (hq : 1 ≤ q) {F G : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c)
    (hG : G ∈ paPoly c) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a : EuclideanSpace ℂ ι,
      Integrable (fun v => ‖paU q a F v‖ * ‖G v‖ * paW q v) ∧
      ∫ v, ‖paU q a F v‖ * ‖G v‖ * paW q v ≤
        C * ((1 + ‖a‖) ^ (2 * c) * Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 4)) := by sorry
