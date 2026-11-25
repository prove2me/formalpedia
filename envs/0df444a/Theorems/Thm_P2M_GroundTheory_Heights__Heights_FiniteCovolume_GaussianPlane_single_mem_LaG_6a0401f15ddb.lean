-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_single_mem_LaG_6a0401f15ddb
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_single_mem_LaG_6a0401f15ddb
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:14:37.245839+00:00
-- url     : https://prove2.me/theorems/731efef5-dda1-406c-977b-22cd1cb1b69b
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane single mem La G 6a0401f15ddb: P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane single mem La G 6a0401f15ddb
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane single mem La G 6a0401f15ddb construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane single mem La G 6a0401f15ddb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L121-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L121-L129

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_single_mem_LaG_6a0401f15ddb (i : Fin 2) : (Pi.single i 1 : Fin 2 → Eg) ∈ LaG := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«GaussianPlane».«single_mem_LaG» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_single_mem_LaG_6a0401f15ddb
