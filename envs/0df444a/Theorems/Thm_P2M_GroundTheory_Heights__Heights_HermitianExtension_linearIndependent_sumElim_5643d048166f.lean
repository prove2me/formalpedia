-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_linearIndependent_sumElim_5643d048166f
-- name    : P2M_GroundTheory_Heights__Heights_HermitianExtension_linearIndependent_sumElim_5643d048166f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:56.80573+00:00
-- url     : https://prove2.me/theorems/9ba18909-6a38-5ce2-95d9-41b24412adf8
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Extension linear Independent sum Elim 5643d048166f: P2 M Ground Theory Heights  Heights Hermitian Extension linear Independent sum Elim 5643d048166f
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Extension linear Independent sum Elim 5643d048166f construction uses the P2 M Ground Theory Heights  Heights Hermitian Extension linear Independent sum Elim 5643d048166f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeExact.lean#L127-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeExact.lean#L127-L146

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
variable {m n : Type*} [Fintype m] [Fintype n]

theorem P2M_GroundTheory_Heights__Heights_HermitianExtension_linearIndependent_sumElim_5643d048166f {s' : m → E'.carrier} {s'' : n → E''.carrier}
    {u : n → E.carrier} (hu : ∀ j, X.proj (u j) = s'' j) (hs' : LinearIndependent (𝓞 K) s')
    (hs'' : LinearIndependent (𝓞 K) s'') :
    LinearIndependent (𝓞 K) (Sum.elim (fun i ↦ X.incl (s' i)) u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianExtension».«linearIndependent_sumElim» := P2M_GroundTheory_Heights__Heights_HermitianExtension_linearIndependent_sumElim_5643d048166f
