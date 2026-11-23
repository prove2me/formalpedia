-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_appLE_of_eq
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.TG.appLE_of_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:48.136778+00:00
-- url     : https://prove2.me/theorems/adee13eb-defd-4632-82e6-f8fff09f4c45
-- title:
--   TG: app LE of eq
-- statement:
--   The TG construction uses the app LE of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenFlat.lean#L143-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenFlat.lean#L143-L145

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.TG.appLE_of_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) {U : Y.Opens} {W : X.Opens}
    (e : W ≤ f ⁻¹ᵁ U) : f.appLE U W e = g.appLE U W (h ▸ e) := by sorry
