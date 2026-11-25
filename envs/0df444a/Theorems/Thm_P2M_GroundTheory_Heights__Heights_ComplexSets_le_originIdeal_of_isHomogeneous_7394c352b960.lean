-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_le_originIdeal_of_isHomogeneous_7394c352b960
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_le_originIdeal_of_isHomogeneous_7394c352b960
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:16:23.615867+00:00
-- url     : https://prove2.me/theorems/116f1240-9513-5a7c-9f58-70c6a7fd88b9
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets le origin Ideal of is Homogeneous 7394c352b960: P2 M Ground Theory Heights  Heights Complex Sets le origin Ideal of is Homogeneous 7394c352b960
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets le origin Ideal of is Homogeneous 7394c352b960 construction uses the P2 M Ground Theory Heights  Heights Complex Sets le origin Ideal of is Homogeneous 7394c352b960 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHomogDimZeroPow.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHomogDimZeroPow.lean#L13-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHomogDimZeroPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_le_originIdeal_of_isHomogeneous_7394c352b960 {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ)) (hne : I ≠ ⊤) : I ≤ originIdeal n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«le_originIdeal_of_isHomogeneous» := P2M_GroundTheory_Heights__Heights_ComplexSets_le_originIdeal_of_isHomogeneous_7394c352b960
