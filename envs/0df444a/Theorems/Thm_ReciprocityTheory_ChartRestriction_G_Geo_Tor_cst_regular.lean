-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cst_regular
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst_regular
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:09.745572+00:00
-- url     : https://prove2.me/theorems/7e032032-b809-4c11-a2a6-903649d83907
-- title:
--   Tor: cst regular
-- statement:
--   The Tor construction uses the cst regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DivCalc.lean#L170-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DivCalc.lean#L170-L201

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi
variable {V : Type} [CommRing V] {X Z : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst_regular [IsDomain V] (p : X ⟶ Sp V) [Flat p] (x : X) {a : V} (ha : a ≠ 0) : IsLeftRegular (cst p x a) := by sorry
