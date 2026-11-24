-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_isDominant_jF
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.TG.isDominant_jF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:59.486239+00:00
-- url     : https://prove2.me/theorems/c4b6c1ed-e334-4a90-91f8-69938c75f346
-- title:
--   TG: is Dominant j F
-- statement:
--   The TG construction uses the is Dominant j F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenFlat.lean#L170-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenFlat.lean#L170-L182

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
noncomputable section
variable {R : Type} [CommRing R] [IsDomain R]

theorem ReciprocityTheory.ChartRestriction.G.DVR.TG.isDominant_jF (R : Type) [CommRing R] [IsDomain R] : IsDominant (jF R) := by sorry
