-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_degree_submodule_le_fccfab8f4814
-- name    : P2M_GroundTheory_Heights__Heights_HermitianExtension_degree_submodule_le_fccfab8f4814
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:19.228448+00:00
-- url     : https://prove2.me/theorems/4d6bb763-a67b-57f5-b8a3-bce1ba695d22
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Extension degree submodule le fccfab8f4814: P2 M Ground Theory Heights  Heights Hermitian Extension degree submodule le fccfab8f4814
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Extension degree submodule le fccfab8f4814 construction uses the P2 M Ground Theory Heights  Heights Hermitian Extension degree submodule le fccfab8f4814 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/LinearIndependentSumElimOfExact.lean#L242-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/LinearIndependentSumElimOfExact.lean#L242-L289

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

theorem P2M_GroundTheory_Heights__Heights_HermitianExtension_degree_submodule_le_fccfab8f4814 : E.degree F ≤ E'.degree (F.comap X.incl) + E''.degree (F.map X.proj) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianExtension».«degree_submodule_le» := P2M_GroundTheory_Heights__Heights_HermitianExtension_degree_submodule_le_fccfab8f4814
