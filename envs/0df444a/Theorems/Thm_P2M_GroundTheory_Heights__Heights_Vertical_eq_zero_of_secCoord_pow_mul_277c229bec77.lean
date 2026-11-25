-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_eq_zero_of_secCoord_pow_mul_277c229bec77
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_eq_zero_of_secCoord_pow_mul_277c229bec77
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:44:42.350792+00:00
-- url     : https://prove2.me/theorems/921290aa-47d7-5987-9274-81d0457f8d55
-- title:
--   P2 M Ground Theory Heights  Heights Vertical eq zero of sec Coord pow mul 277c229bec77: P2 M Ground Theory Heights  Heights Vertical eq zero of sec Coord pow mul 277c229bec77
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical eq zero of sec Coord pow mul 277c229bec77 construction uses the P2 M Ground Theory Heights  Heights Vertical eq zero of sec Coord pow mul 277c229bec77 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBTorsionFree.lean#L27-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBTorsionFree.lean#L27-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBTorsionFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
variable {R : Type*} [CommRing R] {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Vertical_eq_zero_of_secCoord_pow_mul_277c229bec77 (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R)
    (b : SecAlg Q y) (h : ∀ j, ∃ N : ℕ, secCoord Q y j ^ N * b = 0) : b = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«eq_zero_of_secCoord_pow_mul» := P2M_GroundTheory_Heights__Heights_Vertical_eq_zero_of_secCoord_pow_mul_277c229bec77
