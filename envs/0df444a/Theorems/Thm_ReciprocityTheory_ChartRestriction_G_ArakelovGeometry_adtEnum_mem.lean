-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adtEnum_mem
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adtEnum_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:46:14.395872+00:00
-- url     : https://prove2.me/theorems/5d7ac07b-10d0-5591-8f34-97d32ba13c17
-- title:
--   Arakelov Geometry: adt Enum mem
-- statement:
--   The Arakelov Geometry construction uses the adt Enum mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStD.lean#L98-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStD.lean#L98-L100

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adtEnum_mem (D N : ℕ) (i : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card) :
    adtEnum D N i ∈ Finset.Nat.antidiagonalTuple (D + 1) N := by sorry
