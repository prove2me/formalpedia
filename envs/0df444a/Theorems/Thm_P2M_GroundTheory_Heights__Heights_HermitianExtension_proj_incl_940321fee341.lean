-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_proj_incl_940321fee341
-- name    : P2M_GroundTheory_Heights__Heights_HermitianExtension_proj_incl_940321fee341
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:52.580564+00:00
-- url     : https://prove2.me/theorems/99615709-e6bd-4272-81c2-7ee9f406ef7c
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Extension proj incl 940321fee341: P2 M Ground Theory Heights  Heights Hermitian Extension proj incl 940321fee341
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Extension proj incl 940321fee341 construction uses the P2 M Ground Theory Heights  Heights Hermitian Extension proj incl 940321fee341 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeExact.lean#L107-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeExact.lean#L107-L107

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Heights₂.Heights.HermitianExtension
variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')

theorem P2M_GroundTheory_Heights__Heights_HermitianExtension_proj_incl_940321fee341 (y : E'.carrier) : X.proj (X.incl y) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianExtension».«proj_incl» := P2M_GroundTheory_Heights__Heights_HermitianExtension_proj_incl_940321fee341
