-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_subIncl_injective_254710e4ea21
-- name    : P2M_GroundTheory_Heights__Heights_HermitianExtension_subIncl_injective_254710e4ea21
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:14:08.831743+00:00
-- url     : https://prove2.me/theorems/94473632-fd64-4160-b6c4-a515c357bf28
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Extension sub Incl injective 254710e4ea21: P2 M Ground Theory Heights  Heights Hermitian Extension sub Incl injective 254710e4ea21
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Extension sub Incl injective 254710e4ea21 construction uses the P2 M Ground Theory Heights  Heights Hermitian Extension sub Incl injective 254710e4ea21 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/LinearIndependentSumElimOfExact.lean#L219-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/LinearIndependentSumElimOfExact.lean#L219-L220

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

theorem P2M_GroundTheory_Heights__Heights_HermitianExtension_subIncl_injective_254710e4ea21 : Function.Injective (X.subIncl F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianExtension».«subIncl_injective» := P2M_GroundTheory_Heights__Heights_HermitianExtension_subIncl_injective_254710e4ea21
