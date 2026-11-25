-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_tof_covol_lb
-- name    : ReciprocityTheory.ChartRestriction.G.I2.tof_covol_lb
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T15:41:22.027656+00:00
-- url     : https://prove2.me/theorems/0730d730-0b67-54ed-8a98-0055ec84ad9e
-- title:
--   I2: tof covol lb
-- statement:
--   The I2 construction uses the tof covol lb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TofCovolLb.lean#L11-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TofCovolLb.lean#L11-L83

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_OneLeKappaMulPhase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofCovolLb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.tof_covol_lb [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hG : Ext.GHadamard)
    (ob : OrthonormalBasis (Fin (Module.finrank ℝ (IR I))) ℝ (IR I))
    (a : Fin (Module.finrank ℝ (IR I)) → IR I) (ha : ∀ i, (a i : Vsp X.dim) ∈ I)
    (hdet : ob.toBasis.det a ≠ 0) :
    1 ≤ |ob.toBasis.det a| * Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph /
      (2 * PT.f E)) ^ Module.finrank ℝ (IR I) := by sorry
