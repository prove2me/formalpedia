-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_height_eq_ringKrullDim_of_forall
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_eq_ringKrullDim_of_forall
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:47.820946+00:00
-- url     : https://prove2.me/theorems/79de44ba-212c-4a08-a4d4-71936a23d54e
-- title:
--   Dim F: height eq ring Krull Dim of forall
-- statement:
--   The Dim F construction uses the height eq ring Krull Dim of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAB.lean#L34-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAB.lean#L34-L55

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_IsCMOfIsRegularLocalRing
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_RingKrullDimLocalizationQuotientEqHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAB
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

theorem ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_eq_ringKrullDim_of_forall {B : Type*} [CommRing B]
    (hB : ∀ M N : Ideal B, M.IsMaximal → N.IsMaximal → M.height = N.height)
    (M : Ideal B) (hM : M.IsMaximal) : (M.height : WithBot ℕ∞) = ringKrullDim B := by sorry
