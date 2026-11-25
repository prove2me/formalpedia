-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_FiniteLocalHoms_isLocalHom_of_section
-- name    : ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms.isLocalHom_of_section
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:14:26.23551+00:00
-- url     : https://prove2.me/theorems/c7f15416-f841-4dd6-a400-2b098f240c82
-- title:
--   Finite Local Homs: is Local Hom of section
-- statement:
--   The Finite Local Homs construction uses the is Local Hom of section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/FiniteLocalLifts/IsLocalHomAlgebraMap.lean#L11-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/FiniteLocalLifts/IsLocalHomAlgebraMap.lean#L11-L25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_FiniteLocalLifts_IsLocalHomAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open IsLocalRing
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms
variable {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [IsLocalRing R] [Algebra O R]

theorem ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms.isLocalHom_of_section (χ : R →ₐ[O] O) : IsLocalHom (χ : R →+* O) := by sorry
