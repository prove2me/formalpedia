-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_exists_height_of_isMaximal_of_field
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.DimF.exists_height_of_isMaximal_of_field
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:03.033188+00:00
-- url     : https://prove2.me/theorems/d4f9c626-320c-4df0-b431-0e22e9f0d521
-- title:
--   Dim F: exists height of is Maximal of field
-- statement:
--   The Dim F construction uses the exists height of is Maximal of field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAC.lean#L72-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAC.lean#L72-L88

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
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
open Ideal

theorem ReciprocityTheory.ChartRestriction.G.Geo.DimF.exists_height_of_isMaximal_of_field (k B : Type*) [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] :
    ∃ s : ℕ, ∀ M : Ideal B, M.IsMaximal → M.height = s := by sorry
