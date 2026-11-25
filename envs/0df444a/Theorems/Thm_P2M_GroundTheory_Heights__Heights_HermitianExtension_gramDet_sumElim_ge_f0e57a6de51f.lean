-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_gramDet_sumElim_ge_f0e57a6de51f
-- name    : P2M_GroundTheory_Heights__Heights_HermitianExtension_gramDet_sumElim_ge_f0e57a6de51f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:02.701277+00:00
-- url     : https://prove2.me/theorems/ac6fed0c-db4c-5352-bc98-0bee2fe8cec4
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Extension gram Det sum Elim ge f0e57a6de51f: P2 M Ground Theory Heights  Heights Hermitian Extension gram Det sum Elim ge f0e57a6de51f
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Extension gram Det sum Elim ge f0e57a6de51f construction uses the P2 M Ground Theory Heights  Heights Hermitian Extension gram Det sum Elim ge f0e57a6de51f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/LinearIndependentSumElimOfExact.lean#L157-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/LinearIndependentSumElimOfExact.lean#L157-L211

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

theorem P2M_GroundTheory_Heights__Heights_HermitianExtension_gramDet_sumElim_ge_f0e57a6de51f (σ : K →+* ℂ) {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (s' : m → E'.carrier) (u : n → E.carrier) :
    gramDet E'.metric σ s' * gramDet E''.metric σ (fun j ↦ X.proj (u j)) ≤
      gramDet E.metric σ (Sum.elim (fun k ↦ X.incl (s' k)) u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianExtension».«gramDet_sumElim_ge» := P2M_GroundTheory_Heights__Heights_HermitianExtension_gramDet_sumElim_ge_f0e57a6de51f
