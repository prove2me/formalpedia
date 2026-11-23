-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_app_fst_jF_injective
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.TG.app_fst_jF_injective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:39.248808+00:00
-- url     : https://prove2.me/theorems/f60ee1d8-42ba-4d04-8384-5050bc818936
-- title:
--   TG: app fst j F injective
-- statement:
--   The TG construction uses the app fst j F injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenFlat.lean#L184-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenFlat.lean#L184-L188

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.TG.app_fst_jF_injective {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] (U : X.Opens) :
    Function.Injective ((pullback.fst p (jF R)).app U) := by sorry
