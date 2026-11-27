-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_VVG_stable_24276cb2b00a
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_VVG_stable_24276cb2b00a
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:28:12.752882+00:00
-- url     : https://prove2.me/theorems/b0938206-873e-5971-8142-e5cbfc8267c8
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane VVG stable 24276cb2b00a: P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane VVG stable 24276cb2b00a
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane VVG stable 24276cb2b00a construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane VVG stable 24276cb2b00a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L329-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L329-L331

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_VVG_stable_24276cb2b00a : ∀ γ ∈ latticeStab hG LaG, ∀ x ∈ VVG, γ • x ∈ VVG := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«GaussianPlane».«VVG_stable» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_VVG_stable_24276cb2b00a
