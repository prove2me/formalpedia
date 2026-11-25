-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_uc_sep
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Col.uc_sep
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:27:02.130807+00:00
-- url     : https://prove2.me/theorems/19f092a2-f958-5bef-9192-4adef9abae4b
-- title:
--   Col: uc sep
-- statement:
--   The Col construction uses the uc sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean#L200-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean#L200-L208

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

theorem ReciprocityTheory.ChartRestriction.G.I2.Col.uc_sep {y y' : Vsp X.dim} (hy : y ∈ X.L) (hy' : y' ∈ X.L)
    (hne : uc (IR I) y ≠ uc (IR I) y') :
    Real.sqrt (b0 (E := E) P.q P.R0) ≤ dist (uc (IR I) y) (uc (IR I) y') := by sorry
