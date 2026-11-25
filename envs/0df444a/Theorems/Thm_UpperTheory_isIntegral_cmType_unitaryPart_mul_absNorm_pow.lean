-- Prove2me | Theorems.Thm_UpperTheory_isIntegral_cmType_unitaryPart_mul_absNorm_pow
-- name    : UpperTheory.isIntegral_cmType_unitaryPart_mul_absNorm_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:13:27.259593+00:00
-- url     : https://prove2.me/theorems/86a02d47-2142-4ba6-b78e-a00f60f47297
-- title:
--   Upper Theory: is Integral cm Type unitary Part mul abs Norm pow
-- statement:
--   The Upper Theory construction uses the is Integral cm Type unitary Part mul abs Norm pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DivisorFrames/IsIntegralCmTypeUnitaryPartMulAbsNormPow.lean#L91-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DivisorFrames/IsIntegralCmTypeUnitaryPartMulAbsNormPow.lean#L91-L152

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharProd
import Definitions.Def_Development_AutomorphicArithmetic_DivisorFrames_IsIntegralCmTypeUnitaryPartMulAbsNormPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain

theorem UpperTheory.isIntegral_cmType_unitaryPart_mul_absNorm_pow :
    ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), Function.Injective (Sum.elim φ fun i => ComplexEmbedding.conjugate (φ i)) → ∀ (n : I → ℤ) (M : ℕ), (∀ i, (n i).natAbs ≤ M) → ∀ (P : HeightOneSpectrum (𝓞 E)) (h : ℕ) (z : Eˣ), P.valuation E (z : E) = WithZero.exp (-(h : ℤ)) → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.valuation E (z : E) = 1) → IsIntegral ℤ ((∏ i, (φ i (z : E) / ((‖φ i (z : E)‖ : ℝ) : ℂ)) ^ n i) * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (h * M)) := by sorry
