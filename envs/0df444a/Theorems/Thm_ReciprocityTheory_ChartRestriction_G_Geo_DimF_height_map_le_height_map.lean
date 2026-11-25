-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_height_map_le_height_map
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_map_le_height_map
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:23:00.59566+00:00
-- url     : https://prove2.me/theorems/ab46770c-835f-4a45-97af-9135c0f77c50
-- title:
--   Dim F: height map le height map
-- statement:
--   The Dim F construction uses the height map le height map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAA.lean#L55-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAA.lean#L55-L89

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_map_le_height_map {I q M : Ideal A} [q.IsPrime] [M.IsPrime] (hIq : I ≤ q)
    (hqM : q ≤ M) (H : ∀ P : Ideal A, P.IsPrime → I ≤ P → P ≤ M → q ≤ P) :
    (M.map (Ideal.Quotient.mk I)).height ≤ (M.map (Ideal.Quotient.mk q)).height := by sorry
