-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_gap_le_norm_proj_two
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Col.gap_le_norm_proj_two
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:53:41.886157+00:00
-- url     : https://prove2.me/theorems/533c559f-0466-4f53-9c3b-742c16105394
-- title:
--   Col: gap le norm proj two
-- statement:
--   The Col construction uses the gap le norm proj two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean#L128-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean#L128-L133

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

theorem ReciprocityTheory.ChartRestriction.G.I2.Col.gap_le_norm_proj_two {x : Vsp X.dim} (hx : x ∈ Ip X I) (hxI : x ∉ I) : P.th ≤ ‖p2 (IR I) x‖ := by sorry
