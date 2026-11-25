-- Prove2me | Theorems.Thm_UpperTheory_hermitian_diagonalisation
-- name    : UpperTheory.hermitian_diagonalisation
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:12:37.755973+00:00
-- url     : https://prove2.me/theorems/cf4fc9ca-18a4-5627-9b73-daeccaa4313c
-- title:
--   Upper Theory: hermitian diagonalisation
-- statement:
--   The Upper Theory construction uses the hermitian diagonalisation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/HermitianDiagonalisation.lean#L144-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/HermitianDiagonalisation.lean#L144-L190

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HermitianDiagonalisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.hermitian_diagonalisation :
    ∀ {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero E] (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → (∀ x, σ x = x → x ∈ (algebraMap F E).range) → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), (∀ i j, σ (T j i) = T i j) → T.det ≠ 0 → ∃ (g : GL (Fin n) E) (D : Fin n → Fˣ), Matrix.transpose ((g : Matrix (Fin n) (Fin n) E).map σ) * T * (g : Matrix (Fin n) (Fin n) E) = Matrix.diagonal fun i => algebraMap F E (D i : F) := by sorry
