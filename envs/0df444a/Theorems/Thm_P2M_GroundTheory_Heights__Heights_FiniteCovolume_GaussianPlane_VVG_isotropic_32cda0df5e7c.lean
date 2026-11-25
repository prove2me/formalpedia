-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_VVG_isotropic_32cda0df5e7c
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_VVG_isotropic_32cda0df5e7c
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:34:40.576396+00:00
-- url     : https://prove2.me/theorems/c92fbb7c-4e7d-5898-b74f-f6a930ecbbf8
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane VVG isotropic 32cda0df5e7c: P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane VVG isotropic 32cda0df5e7c
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane VVG isotropic 32cda0df5e7c construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane VVG isotropic 32cda0df5e7c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L338-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L338-L342

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_VVG_isotropic_32cda0df5e7c : ∀ x ∈ VVG, x ≠ 0 ∧ hG.toSesq x x = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«GaussianPlane».«VVG_isotropic» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_VVG_isotropic_32cda0df5e7c
