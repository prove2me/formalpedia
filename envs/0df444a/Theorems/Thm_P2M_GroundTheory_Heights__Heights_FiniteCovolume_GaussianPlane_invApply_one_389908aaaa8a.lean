-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_invApply_one_389908aaaa8a
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_invApply_one_389908aaaa8a
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:23:49.525669+00:00
-- url     : https://prove2.me/theorems/f76486b3-c404-497b-adef-7ddd74fee61d
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane inv Apply one 389908aaaa8a: P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane inv Apply one 389908aaaa8a
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane inv Apply one 389908aaaa8a construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane inv Apply one 389908aaaa8a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L221-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L221-L224

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_invApply_one_389908aaaa8a (y : InfinitePlace Eg → Fin 2 → ℂ) :
    invApply (1 : archUnitary hG vG) y = y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«GaussianPlane».«invApply_one» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_invApply_one_389908aaaa8a
