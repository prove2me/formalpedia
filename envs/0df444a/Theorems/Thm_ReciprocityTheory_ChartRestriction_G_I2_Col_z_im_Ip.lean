-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_z_im_Ip
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Col.z_im_Ip
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:06.356778+00:00
-- url     : https://prove2.me/theorems/ceedc2e4-103c-4703-8a1e-8780c1a864fd
-- title:
--   Col: z im Ip
-- statement:
--   The Col construction uses the z im Ip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean#L43-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean#L43-L44

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
variable (X : PT E) (I : Submodule ℤ (Vsp X.dim))
variable {X I}

theorem ReciprocityTheory.ChartRestriction.G.I2.Col.z_im_Ip {x : Vsp X.dim} (hx : x ∈ Ip X I) (k : Fin (dK (IR I))) : (z (IR I) k x).im = 0 := by sorry
