-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_vecAt_apply_44afb2b4bdbb
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_vecAt_apply_44afb2b4bdbb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:54:14.062792+00:00
-- url     : https://prove2.me/theorems/7bd7021d-5f28-5dc4-9d58-f0f5e3d474c7
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane vec At apply 44afb2b4bdbb: P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane vec At apply 44afb2b4bdbb
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane vec At apply 44afb2b4bdbb construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane vec At apply 44afb2b4bdbb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L226-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L226-L228

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_vecAt_apply_44afb2b4bdbb (x : Fin 2 → Eg) (w : InfinitePlace Eg) (i : Fin 2) :
    vecAt vG x w i = w.embedding (x i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«GaussianPlane».«vecAt_apply» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_vecAt_apply_44afb2b4bdbb
