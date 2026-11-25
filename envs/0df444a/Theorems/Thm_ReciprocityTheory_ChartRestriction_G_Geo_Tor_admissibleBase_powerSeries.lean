-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_admissibleBase_powerSeries
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.admissibleBase_powerSeries
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:47.494126+00:00
-- url     : https://prove2.me/theorems/b6b9c9a1-8072-4ae7-8836-2e7e49f14cee
-- title:
--   Tor: admissible Base power Series
-- statement:
--   The Tor construction uses the admissible Base power Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/AdmissibleBasePowerSeries.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/AdmissibleBasePowerSeries.lean#L12-L17

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabMapCubical
import Definitions.Def_ReciprocityTheory_AdicCompleteness_IsAdicCompleteComapConstantCoeff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AdmissibleBasePowerSeries
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.admissibleBase_powerSeries (k : Type) [Field k] : Out.AdmBase (PowerSeries k) (Ideal.span {PowerSeries.X}) := by sorry
