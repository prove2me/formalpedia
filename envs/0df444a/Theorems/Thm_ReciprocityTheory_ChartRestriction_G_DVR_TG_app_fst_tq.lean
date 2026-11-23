-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_app_fst_tq
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.TG.app_fst_tq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:42.204946+00:00
-- url     : https://prove2.me/theorems/f75918d4-92d5-414c-99c8-f8584cc9532a
-- title:
--   TG: app fst tq
-- statement:
--   The TG construction uses the app fst tq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenFlat.lean#L72-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenFlat.lean#L72-L133

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
variable {R : Type} [CommRing R]

theorem ReciprocityTheory.ChartRestriction.G.DVR.TG.app_fst_tq {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (J : Ideal R) (W : X.Opens)
    (hW : IsAffineOpen W) :
    Function.Surjective ((pullback.fst p (tq J)).app W) ∧
      ∀ x, (pullback.fst p (tq J)).app W x = 0 → x ∈ J.map (toW p W) := by sorry
