-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_continuous_secFun
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.continuous_secFun
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:48.396353+00:00
-- url     : https://prove2.me/theorems/6d0c4c98-0b1d-45b9-8311-633470e0e32d
-- title:
--   Arakelov Geometry: continuous sec Fun
-- statement:
--   The Arakelov Geometry construction uses the continuous sec Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ABridgeStA.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ABridgeStA.lean#L40-L42

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStA
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module
variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.continuous_secFun (b : MvPolynomial J ℚ) : Continuous (secFun b) := by sorry
