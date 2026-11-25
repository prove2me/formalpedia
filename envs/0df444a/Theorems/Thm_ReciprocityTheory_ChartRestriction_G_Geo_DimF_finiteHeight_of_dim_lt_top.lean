-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_finiteHeight_of_dim_lt_top
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.DimF.finiteHeight_of_dim_lt_top
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:23:03.455705+00:00
-- url     : https://prove2.me/theorems/e474e579-0579-41b3-b174-5ecdd757c068
-- title:
--   Dim F: finite Height of dim lt top
-- statement:
--   The Dim F construction uses the finite Height of dim lt top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAA.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAA.lean#L17-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.DimF
variable {A : Type*} [CommRing A]

theorem ReciprocityTheory.ChartRestriction.G.Geo.DimF.finiteHeight_of_dim_lt_top {B : Type*} [CommRing B] (I : Ideal B) (hI : I ≠ ⊤)
    (h : ringKrullDim B < ⊤) : I.FiniteHeight := by sorry
