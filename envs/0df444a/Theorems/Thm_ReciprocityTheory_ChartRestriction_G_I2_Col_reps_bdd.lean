-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_reps_bdd
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Col.reps_bdd
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:31:21.479887+00:00
-- url     : https://prove2.me/theorems/9369b560-aec2-48a1-a1f1-215032ea6832
-- title:
--   Col: reps bdd
-- statement:
--   The Col construction uses the reps bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean#L210-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean#L210-L243

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_MemOfProjTwoEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex NumberField
open scoped InnerProductSpace
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.Col
variable {E : Type} [Field E] [NumberField E]
variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF}
variable (hI : IsSplit P I)
include hI

theorem ReciprocityTheory.ChartRestriction.G.I2.Col.reps_bdd (hP : Ext.PackingCount) (C : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ y ∈ X.L, ‖uc (IR I) y‖ ≤ C →
      ∃ y' ∈ X.L, uc (IR I) y' = uc (IR I) y ∧ ‖p2 (IR I) y'‖ ≤ M := by sorry
