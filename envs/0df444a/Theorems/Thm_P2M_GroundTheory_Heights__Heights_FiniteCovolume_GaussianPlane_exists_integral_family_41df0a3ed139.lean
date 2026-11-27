-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_exists_integral_family_41df0a3ed139
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_exists_integral_family_41df0a3ed139
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:34:24.185399+00:00
-- url     : https://prove2.me/theorems/71f7c586-08b3-5fdc-bbf1-4604cc89f632
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane exists integral family 41df0a3ed139: P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane exists integral family 41df0a
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane exists integral family 41df0a3ed139 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane exists integral family 41df0a3ed139 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L306-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L306-L325

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_exists_integral_family_41df0a3ed139 : ∃ r : ℝ, ∃ a : Fin (2 * finrank ℚ ℚ) → 𝓞 Eg,
    LinearIndependent ℚ (fun i => (a i : Eg)) ∧ ∀ i (σ : Eg →+* ℂ), ‖σ (a i)‖ ≤ r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«GaussianPlane».«exists_integral_family» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_exists_integral_family_41df0a3ed139
