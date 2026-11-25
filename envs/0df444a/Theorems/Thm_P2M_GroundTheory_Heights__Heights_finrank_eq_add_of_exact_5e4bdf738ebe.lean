-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_finrank_eq_add_of_exact_5e4bdf738ebe
-- name    : P2M_GroundTheory_Heights__Heights_finrank_eq_add_of_exact_5e4bdf738ebe
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:46:14.454819+00:00
-- url     : https://prove2.me/theorems/41a8abee-469f-566a-8dd2-e72b1ec51883
-- title:
--   P2 M Ground Theory Heights  Heights finrank eq add of exact 5e4bdf738ebe: P2 M Ground Theory Heights  Heights finrank eq add of exact 5e4bdf738ebe
-- statement:
--   The P2 M Ground Theory Heights  Heights finrank eq add of exact 5e4bdf738ebe construction uses the P2 M Ground Theory Heights  Heights finrank eq add of exact 5e4bdf738ebe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/LinearIndependentSumElimOfExact.lean#L40-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/LinearIndependentSumElimOfExact.lean#L40-L52

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
omit [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_finrank_eq_add_of_exact_5e4bdf738ebe [Module.Finite (𝓞 K) A] [Module.Finite (𝓞 K) B]
    [Module.Finite (𝓞 K) C] (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p) :
    Module.finrank (𝓞 K) B = Module.finrank (𝓞 K) A + Module.finrank (𝓞 K) C := by sorry

alias «GroundTheory».«Heights₂».«Heights».«finrank_eq_add_of_exact» := P2M_GroundTheory_Heights__Heights_finrank_eq_add_of_exact_5e4bdf738ebe
