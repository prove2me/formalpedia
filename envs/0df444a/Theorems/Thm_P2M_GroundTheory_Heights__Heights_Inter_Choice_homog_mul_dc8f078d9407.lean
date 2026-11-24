-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_mul_dc8f078d9407
-- name    : P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_mul_dc8f078d9407
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:04.414126+00:00
-- url     : https://prove2.me/theorems/190fc819-eb3d-4dcb-a112-b89b559f831c
-- title:
--   P2 M Ground Theory Heights  Heights Inter Choice homog mul dc8f078d9407: P2 M Ground Theory Heights  Heights Inter Choice homog mul dc8f078d9407
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Choice homog mul dc8f078d9407 construction uses the P2 M Ground Theory Heights  Heights Inter Choice homog mul dc8f078d9407 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChoice.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChoice.lean#L15-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChoice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter.Choice
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_mul_dc8f078d9407 {f g : MRingOver R ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«Choice».«homog_mul» := P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_mul_dc8f078d9407
