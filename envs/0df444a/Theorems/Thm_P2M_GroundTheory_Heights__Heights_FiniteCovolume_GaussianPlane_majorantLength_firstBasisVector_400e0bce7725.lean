-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_majorantLength_firstBasisVector_400e0bce7725
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_majorantLength_firstBasisVector_400e0bce7725
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:39:26.569058+00:00
-- url     : https://prove2.me/theorems/0e1947c6-4a7a-41e6-b500-c513f1119d68
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane majorant Length first Basis Vector 400e0bce7725: P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane majorant Length f
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane majorant Length first Basis Vector 400e0bce7725 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane majorant Length first Basis Vector 400e0bce7725 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L289-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L289-L292

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_majorantLength_firstBasisVector_400e0bce7725 : MG.len (invApply (1 : archUnitary hG vG) (vecAt vG e0)) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«GaussianPlane».«majorantLength_firstBasisVector» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_majorantLength_firstBasisVector_400e0bce7725
