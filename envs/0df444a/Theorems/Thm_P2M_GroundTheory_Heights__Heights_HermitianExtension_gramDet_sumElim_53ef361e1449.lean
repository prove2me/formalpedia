-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_gramDet_sumElim_53ef361e1449
-- name    : P2M_GroundTheory_Heights__Heights_HermitianExtension_gramDet_sumElim_53ef361e1449
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:51.058301+00:00
-- url     : https://prove2.me/theorems/42fa5f8e-dc6c-553d-9ea8-7e2652d83679
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Extension gram Det sum Elim 53ef361e1449: P2 M Ground Theory Heights  Heights Hermitian Extension gram Det sum Elim 53ef361e1449
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Extension gram Det sum Elim 53ef361e1449 construction uses the P2 M Ground Theory Heights  Heights Hermitian Extension gram Det sum Elim 53ef361e1449 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeExact.lean#L224-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeExact.lean#L224-L286

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
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem P2M_GroundTheory_Heights__Heights_HermitianExtension_gramDet_sumElim_53ef361e1449 (σ : K →+* ℂ) {s' : m → E'.carrier} {s'' : n → E''.carrier}
    {u : n → E.carrier} (hu : ∀ j, X.proj (u j) = s'' j) (hs' : LinearIndependent (𝓞 K) s')
    (hcard' : Fintype.card m = Module.finrank (𝓞 K) E'.carrier) :
    gramDet E.metric σ (Sum.elim (fun i ↦ X.incl (s' i)) u) =
      gramDet E'.metric σ s' * gramDet E''.metric σ s'' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianExtension».«gramDet_sumElim» := P2M_GroundTheory_Heights__Heights_HermitianExtension_gramDet_sumElim_53ef361e1449
