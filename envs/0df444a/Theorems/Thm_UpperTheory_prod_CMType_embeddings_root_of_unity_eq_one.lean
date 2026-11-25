-- Prove2me | Theorems.Thm_UpperTheory_prod_CMType_embeddings_root_of_unity_eq_one
-- name    : UpperTheory.prod_CMType_embeddings_root_of_unity_eq_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:14:05.39557+00:00
-- url     : https://prove2.me/theorems/c075b752-cefa-4a67-8f3f-e6c67666368d
-- title:
--   Upper Theory: prod CMType embeddings root of unity eq one
-- statement:
--   The Upper Theory construction uses the prod CMType embeddings root of unity eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/ProdCMTypeEmbeddingsRootOfUnityEqOne.lean#L7-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/ProdCMTypeEmbeddingsRootOfUnityEqOne.lean#L7-L50

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_IsRootOfIntegral
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdCMTypeEmbeddingsRootOfUnityEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.BasicNotions

theorem UpperTheory.prod_CMType_embeddings_root_of_unity_eq_one :
    ∀ (R : Ranks) (H : Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ),
      (∀ σ : H.E →+* ℂ, ∃! i, σ = φ i ∨ σ = ComplexEmbedding.conjugate (φ i)) → (∀ i j, φ i H.sqd = φ j H.sqd) →
      ∀ z : H.E, (∃ m : ℕ, 0 < m ∧ z ^ m = 1) → ∏ i, φ i z = 1 := by sorry
