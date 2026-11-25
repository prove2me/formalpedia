-- Prove2me | Theorems.Thm_UpperTheory_measurable_matrix_inv
-- name    : UpperTheory.measurable_matrix_inv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:12:45.842839+00:00
-- url     : https://prove2.me/theorems/dd98b87a-1f45-44fb-90ab-790680f30851
-- title:
--   Upper Theory: measurable matrix inv
-- statement:
--   The Upper Theory construction uses the measurable matrix inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MeasurableMatrixInv.lean#L3-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MeasurableMatrixInv.lean#L3-L18

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MeasurableMatrixInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.measurable_matrix_inv :
    ∀ n : ℕ, Measurable (fun x : Fin n → Fin n → ℂ => (Matrix.of.symm ((Matrix.of x : Matrix (Fin n) (Fin n) ℂ)⁻¹) : Fin n → Fin n → ℂ)) := by sorry
