-- Prove2me | Theorems.Thm_UpperTheory_dvd_norm_sub_one_of_idempotent_interpolation_relNorm_one
-- name    : UpperTheory.dvd_norm_sub_one_of_idempotent_interpolation_relNorm_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:07:52.964472+00:00
-- url     : https://prove2.me/theorems/6fd676b4-3402-5318-8695-135a3ccb0bef
-- title:
--   Upper Theory: dvd norm sub one of idempotent interpolation rel Norm one
-- statement:
--   The Upper Theory construction uses the dvd norm sub one of idempotent interpolation rel Norm one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/DvdNormSubOneOfIdempotentInterpolationRelNormOne.lean#L47-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/DvdNormSubOneOfIdempotentInterpolationRelNormOne.lean#L47-L99

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_DvdNormSubOneOfIdempotentInterpolationRelNormOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain

theorem UpperTheory.dvd_norm_sub_one_of_idempotent_interpolation_relNorm_one :
    ∀ (E : Type) [Field E] [NumberField E] (K : IntermediateField ℚ E) (n : ℕ) (e t δ y : 𝓞 E), (e : E) ∈ K → e * e - e = n * t →
      Algebra.norm K (δ : E) = 1 → (n : ℤ) ∣ Algebra.norm ℤ (e * δ + (1 - e) + n * y : 𝓞 E) - 1 := by sorry
