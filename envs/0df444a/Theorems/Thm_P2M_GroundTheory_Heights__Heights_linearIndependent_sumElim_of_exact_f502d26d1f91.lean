-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_linearIndependent_sumElim_of_exact_f502d26d1f91
-- name    : P2M_GroundTheory_Heights__Heights_linearIndependent_sumElim_of_exact_f502d26d1f91
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:48:44.640094+00:00
-- url     : https://prove2.me/theorems/6851aef5-b88c-4d37-9966-f4d8321eb5b2
-- title:
--   P2 M Ground Theory Heights  Heights linear Independent sum Elim of exact f502d26d1f91: P2 M Ground Theory Heights  Heights linear Independent sum Elim of exact f502d26d1f91
-- statement:
--   The P2 M Ground Theory Heights  Heights linear Independent sum Elim of exact f502d26d1f91 construction uses the P2 M Ground Theory Heights  Heights linear Independent sum Elim of exact f502d26d1f91 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/LinearIndependentSumElimOfExact.lean#L58-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/LinearIndependentSumElimOfExact.lean#L58-L77

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
variable {A B C : Type*} [AddCommGroup A] [Module (𝓞 K) A] [AddCommGroup B] [Module (𝓞 K) B]
  [AddCommGroup C] [Module (𝓞 K) C] {i : A →ₗ[𝓞 K] B} {p : B →ₗ[𝓞 K] C}
variable {m n : Type*} [Fintype m] [Fintype n]
omit [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_linearIndependent_sumElim_of_exact_f502d26d1f91 (hi : Function.Injective i) (hex : Function.Exact i p)
    {s' : m → A} {s'' : n → C} {u : n → B} (hu : ∀ j, p (u j) = s'' j)
    (hs' : LinearIndependent (𝓞 K) s') (hs'' : LinearIndependent (𝓞 K) s'') :
    LinearIndependent (𝓞 K) (Sum.elim (fun k ↦ i (s' k)) u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«linearIndependent_sumElim_of_exact» := P2M_GroundTheory_Heights__Heights_linearIndependent_sumElim_of_exact_f502d26d1f91
