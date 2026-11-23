-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_toW_mul_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.TG.toW_mul_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:52.375467+00:00
-- url     : https://prove2.me/theorems/fc5dcbf9-6547-4d84-8a7a-9b3348e73992
-- title:
--   TG: to W mul eq zero
-- statement:
--   The TG construction uses the to W mul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenFlat.lean#L190-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenFlat.lean#L190-L224

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.TG.toW_mul_eq_zero {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] (V : X.Opens)
    {r : R} (hr : r ≠ 0) {y : Γ(X, V)} (h : toW p V r * y = 0) : y = 0 := by sorry
