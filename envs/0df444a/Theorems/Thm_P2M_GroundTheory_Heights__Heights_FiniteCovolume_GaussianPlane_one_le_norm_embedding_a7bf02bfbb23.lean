-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_one_le_norm_embedding_a7bf02bfbb23
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_one_le_norm_embedding_a7bf02bfbb23
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:42:00.761801+00:00
-- url     : https://prove2.me/theorems/03a5da61-abf5-4cdc-9299-b250301c4367
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane one le norm embedding a7bf02bfbb23: P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane one le norm embedding a7bf02bf
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane one le norm embedding a7bf02bfbb23 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane one le norm embedding a7bf02bfbb23 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L70-L73

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Examples
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped Pointwise ComplexOrder ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_one_le_norm_embedding_a7bf02bfbb23 (w : InfinitePlace Eg) {a : 𝓞 Eg} (ha : a ≠ 0) :
    1 ≤ ‖w.embedding (a : Eg)‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«GaussianPlane».«one_le_norm_embedding» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_one_le_norm_embedding_a7bf02bfbb23
