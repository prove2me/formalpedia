-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_rank_sub_eq_155a2f330e2e
-- name    : P2M_GroundTheory_Heights__Heights_HermitianExtension_rank_sub_eq_155a2f330e2e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:59.254245+00:00
-- url     : https://prove2.me/theorems/8a34025a-490c-4703-9baf-857e963d8db7
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Extension rank sub eq 155a2f330e2e: P2 M Ground Theory Heights  Heights Hermitian Extension rank sub eq 155a2f330e2e
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Extension rank sub eq 155a2f330e2e construction uses the P2 M Ground Theory Heights  Heights Hermitian Extension rank sub eq 155a2f330e2e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/LinearIndependentSumElimOfExact.lean#L239-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/LinearIndependentSumElimOfExact.lean#L239-L240

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

theorem P2M_GroundTheory_Heights__Heights_HermitianExtension_rank_sub_eq_155a2f330e2e : E.rank F = E'.rank (F.comap X.incl) + E''.rank (F.map X.proj) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianExtension».«rank_sub_eq» := P2M_GroundTheory_Heights__Heights_HermitianExtension_rank_sub_eq_155a2f330e2e
