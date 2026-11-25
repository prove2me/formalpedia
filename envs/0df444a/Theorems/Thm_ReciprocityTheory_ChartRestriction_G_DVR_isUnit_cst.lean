-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_isUnit_cst
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.isUnit_cst
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:14:15.937738+00:00
-- url     : https://prove2.me/theorems/3cfe5a13-0a95-48c6-b668-0caa1b05a8ff
-- title:
--   DVR: is Unit cst
-- statement:
--   The DVR construction uses the is Unit cst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/NuExtA.lean#L64-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/NuExtA.lean#L64-L74

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThickKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_NuExtA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Out
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {X : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.DVR.isUnit_cst (p : X ⟶ Sp V) (x : X) {r : V} (hx : r ∉ (p x).asIdeal) : IsUnit (cst p x r) := by sorry
