-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_homogeneousComponent_mul_left_b27e51f058a8
-- name    : P2M_GroundTheory_Heights__Heights_KRest_homogeneousComponent_mul_left_b27e51f058a8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:15.559192+00:00
-- url     : https://prove2.me/theorems/1e55e765-47a6-4e8d-a3be-527ff0ecab91
-- title:
--   P2 M Ground Theory Heights  Heights KRest homogeneous Component mul left b27e51f058a8: P2 M Ground Theory Heights  Heights KRest homogeneous Component mul left b27e51f058a8
-- statement:
--   The P2 M Ground Theory Heights  Heights KRest homogeneous Component mul left b27e51f058a8 construction uses the P2 M Ground Theory Heights  Heights KRest homogeneous Component mul left b27e51f058a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/RestCutBasic.lean#L13-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/RestCutBasic.lean#L13-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_RestCutBasic
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
open GroundTheory.Heights₂.Heights.KRest
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_KRest_homogeneousComponent_mul_left_b27e51f058a8 {σ R : Type*} [CommRing R] {P : MvPolynomial σ R} {l : ℕ}
    (hP : P.IsHomogeneous l) (G : MvPolynomial σ R) (d : ℕ) :
    homogeneousComponent d (P * G) =
      if l ≤ d then P * homogeneousComponent (d - l) G else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KRest».«homogeneousComponent_mul_left» := P2M_GroundTheory_Heights__Heights_KRest_homogeneousComponent_mul_left_b27e51f058a8
