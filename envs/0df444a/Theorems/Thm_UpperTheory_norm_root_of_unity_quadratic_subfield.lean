-- Prove2me | Theorems.Thm_UpperTheory_norm_root_of_unity_quadratic_subfield
-- name    : UpperTheory.norm_root_of_unity_quadratic_subfield
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:49:46.853668+00:00
-- url     : https://prove2.me/theorems/6c36b56d-11af-5f58-9fa4-560c8d700fda
-- title:
--   Upper Theory: norm root of unity quadratic subfield
-- statement:
--   The Upper Theory construction uses the norm root of unity quadratic subfield property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/NormRootOfUnityQuadraticSubfield.lean#L214-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/NormRootOfUnityQuadraticSubfield.lean#L214-L221

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ReprMem
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_NormRootOfUnityQuadraticSubfield
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField

theorem UpperTheory.norm_root_of_unity_quadratic_subfield :
    ∀ (E : Type) [Field E] [NumberField E] (s : E) (d : ℕ), d.Prime → 3 < d → s ^ 2 = -(d : E) → 4 ∣ Module.finrank ℚ E →
      ∀ z : E, (∃ m : ℕ, 0 < m ∧ z ^ m = 1) → Algebra.norm ℚ⟮s⟯ z = 1 := by sorry
