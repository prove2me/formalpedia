-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_subExact_03efe69f570c
-- name    : P2M_GroundTheory_Heights__Heights_HermitianExtension_subExact_03efe69f570c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:58.699232+00:00
-- url     : https://prove2.me/theorems/72efc1f9-3f4e-4b60-a3e6-757f0b08d5f3
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Extension sub Exact 03efe69f570c: P2 M Ground Theory Heights  Heights Hermitian Extension sub Exact 03efe69f570c
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Extension sub Exact 03efe69f570c construction uses the P2 M Ground Theory Heights  Heights Hermitian Extension sub Exact 03efe69f570c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/LinearIndependentSumElimOfExact.lean#L226-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/LinearIndependentSumElimOfExact.lean#L226-L237

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open scoped ComplexOrder
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Heights₂.Heights.HermitianExtension
variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')
variable (F : Submodule (𝓞 K) E.carrier)

theorem P2M_GroundTheory_Heights__Heights_HermitianExtension_subExact_03efe69f570c : Function.Exact (X.subIncl F) (X.subProj F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianExtension».«subExact» := P2M_GroundTheory_Heights__Heights_HermitianExtension_subExact_03efe69f570c
