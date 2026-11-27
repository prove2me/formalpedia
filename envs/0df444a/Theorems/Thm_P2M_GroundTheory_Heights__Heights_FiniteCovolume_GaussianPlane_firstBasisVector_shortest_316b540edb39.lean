-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_firstBasisVector_shortest_316b540edb39
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_firstBasisVector_shortest_316b540edb39
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:17:19.697653+00:00
-- url     : https://prove2.me/theorems/16cf46bb-5f9e-51de-926b-8f5379cf73a9
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane first Basis Vector shortest 316b540edb39: P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane first Basis Vector short
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane first Basis Vector shortest 316b540edb39 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane first Basis Vector shortest 316b540edb39 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L294-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L294-L298

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_firstBasisVector_shortest_316b540edb39 (y : Fin 2 → Eg) (hy : y ∈ LaG) (hy0 : y ≠ 0) :
    MG.len (invApply (1 : archUnitary hG vG) (vecAt vG e0)) ≤
      MG.len (invApply (1 : archUnitary hG vG) (vecAt vG y)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«GaussianPlane».«firstBasisVector_shortest» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_firstBasisVector_shortest_316b540edb39
