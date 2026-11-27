-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_FiniteLocalHoms_isLocalHom_algebraMap
-- name    : ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms.isLocalHom_algebraMap
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:14:16.829908+00:00
-- url     : https://prove2.me/theorems/cdf516b6-ac63-4ebc-ad75-aa07c78df00e
-- title:
--   Finite Local Homs: is Local Hom algebra Map
-- statement:
--   The Finite Local Homs construction uses the is Local Hom algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/FiniteLocalLifts/IsLocalHomAlgebraMap.lean#L27-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/FiniteLocalLifts/IsLocalHomAlgebraMap.lean#L27-L38

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

theorem ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms.isLocalHom_algebraMap [Module.Finite O R] : IsLocalHom (algebraMap O R) := by sorry
