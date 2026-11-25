-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_one_le_len_e9003551bcf2
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_one_le_len_e9003551bcf2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:39:24.402691+00:00
-- url     : https://prove2.me/theorems/f52da4c5-ccf5-4fea-8850-13d8d449408e
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane one le len e9003551bcf2: P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane one le len e9003551bcf2
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane one le len e9003551bcf2 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane one le len e9003551bcf2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L230-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L230-L252

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_one_le_len_e9003551bcf2 {x : Fin 2 → Eg} (hx : x ∈ LaG) (hx0 : x ≠ 0) :
    1 ≤ MG.len (invApply (1 : archUnitary hG vG) (vecAt vG x)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«GaussianPlane».«one_le_len» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_one_le_len_e9003551bcf2
