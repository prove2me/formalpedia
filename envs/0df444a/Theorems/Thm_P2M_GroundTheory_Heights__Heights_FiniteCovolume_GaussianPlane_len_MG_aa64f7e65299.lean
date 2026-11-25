-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_len_MG_aa64f7e65299
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_len_MG_aa64f7e65299
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:17:57.7883+00:00
-- url     : https://prove2.me/theorems/1e2dcd21-258b-5200-b990-6e2eb544b450
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane len MG aa64f7e65299: P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane len MG aa64f7e65299
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane len MG aa64f7e65299 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane len MG aa64f7e65299 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L216-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L216-L219

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_len_MG_aa64f7e65299 (y : InfinitePlace Eg → Fin 2 → ℂ) (w : InfinitePlace Eg) :
    MG.len y = Real.sqrt (‖y w 0‖ ^ 2 + ‖y w 1‖ ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«GaussianPlane».«len_MG» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_len_MG_aa64f7e65299
