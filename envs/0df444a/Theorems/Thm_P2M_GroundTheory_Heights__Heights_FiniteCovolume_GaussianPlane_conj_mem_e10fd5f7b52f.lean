-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_conj_mem_e10fd5f7b52f
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_conj_mem_e10fd5f7b52f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:53:59.285262+00:00
-- url     : https://prove2.me/theorems/47b58443-3cc7-4191-a37b-5244a6fd5429
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane conj mem e10fd5f7b52f: P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane conj mem e10fd5f7b52f
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane conj mem e10fd5f7b52f construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane conj mem e10fd5f7b52f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L117-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L117-L119

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_conj_mem_e10fd5f7b52f {z : Eg} (hz : z ∈ integralClosure ℤ Eg) : conj ℚ Eg z ∈ integralClosure ℤ Eg := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«GaussianPlane».«conj_mem» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_conj_mem_e10fd5f7b52f
