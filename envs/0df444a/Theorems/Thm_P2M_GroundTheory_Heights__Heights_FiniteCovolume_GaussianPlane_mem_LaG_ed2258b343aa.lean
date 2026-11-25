-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_mem_LaG_ed2258b343aa
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_mem_LaG_ed2258b343aa
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:51:57.389051+00:00
-- url     : https://prove2.me/theorems/57d76ab8-61b4-5f2d-9d99-43567931396b
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane mem La G ed2258b343aa: P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane mem La G ed2258b343aa
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane mem La G ed2258b343aa construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane mem La G ed2258b343aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L110-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L110-L115

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_mem_LaG_ed2258b343aa {x : Fin 2 → Eg} : x ∈ LaG ↔ ∀ i, x i ∈ integralClosure ℤ Eg := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«GaussianPlane».«mem_LaG» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_mem_LaG_ed2258b343aa
