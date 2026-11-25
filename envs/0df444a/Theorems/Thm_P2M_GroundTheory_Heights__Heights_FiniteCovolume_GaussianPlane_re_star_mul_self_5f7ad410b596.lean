-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_re_star_mul_self_5f7ad410b596
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_re_star_mul_self_5f7ad410b596
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:28:18.915877+00:00
-- url     : https://prove2.me/theorems/296b586a-2eb0-4cba-8d1a-4506ccdbc490
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane re star mul self 5f7ad410b596: P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane re star mul self 5f7ad410b596
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane re star mul self 5f7ad410b596 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane re star mul self 5f7ad410b596 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L212-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L212-L214

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_re_star_mul_self_5f7ad410b596 (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«GaussianPlane».«re_star_mul_self» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_re_star_mul_self_5f7ad410b596
