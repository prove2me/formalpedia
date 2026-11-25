-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_sign_eq_of_proj_two_eq
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Col.sign_eq_of_proj_two_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:27:30.24048+00:00
-- url     : https://prove2.me/theorems/b015ec17-1bb7-4853-9d1b-1540a16833a0
-- title:
--   Col: sign eq of proj two eq
-- statement:
--   The Col construction uses the sign eq of proj two eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean#L149-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean#L149-L156

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

theorem ReciprocityTheory.ChartRestriction.G.I2.Col.sign_eq_of_proj_two_eq {x y : Vsp X.dim} (hx : x ∈ Ip X I) (hy : y ∈ Ip X I)
    (h : p2 (IR I) x = p2 (IR I) y) : X.eps x = X.eps y := by sorry
