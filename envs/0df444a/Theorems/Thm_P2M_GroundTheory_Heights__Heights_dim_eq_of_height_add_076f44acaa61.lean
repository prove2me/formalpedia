-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_dim_eq_of_height_add_076f44acaa61
-- name    : P2M_GroundTheory_Heights__Heights_dim_eq_of_height_add_076f44acaa61
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:48.511339+00:00
-- url     : https://prove2.me/theorems/4155d0be-53a2-4e28-b6f7-0bbe4595509c
-- title:
--   P2 M Ground Theory Heights  Heights dim eq of height add 076f44acaa61: P2 M Ground Theory Heights  Heights dim eq of height add 076f44acaa61
-- statement:
--   The P2 M Ground Theory Heights  Heights dim eq of height add 076f44acaa61 construction uses the P2 M Ground Theory Heights  Heights dim eq of height add 076f44acaa61 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceMultGeneral.lean#L13-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceMultGeneral.lean#L13-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceMultGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMGeneralPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseSliceGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthTransverseSlice
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceMultGeneral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Matrix ComplexSets

theorem P2M_GroundTheory_Heights__Heights_dim_eq_of_height_add_076f44acaa61 {h : ℕ∞} {x : WithBot ℕ∞} {e : ℕ} (h1 : x + 1 ≤ ((e + 1 : ℕ) : WithBot ℕ∞))
    (hh : h ≤ 1) (hsum : (h : WithBot ℕ∞) + x = ((e + 1 : ℕ) : WithBot ℕ∞)) : x = ((e : ℕ) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«dim_eq_of_height_add» := P2M_GroundTheory_Heights__Heights_dim_eq_of_height_add_076f44acaa61
