-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_specFirst_C_mul_fbe46aaee29f
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_specFirst_C_mul_fbe46aaee29f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:43:56.222173+00:00
-- url     : https://prove2.me/theorems/1c927257-7111-47af-b0c5-7b4adde576df
-- title:
--   P2 M Ground Theory Heights  Heights Vertical spec First C mul fbe46aaee29f: P2 M Ground Theory Heights  Heights Vertical spec First C mul fbe46aaee29f
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical spec First C mul fbe46aaee29f construction uses the P2 M Ground Theory Heights  Heights Vertical spec First C mul fbe46aaee29f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/IsChowFormCMul.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/IsChowFormCMul.lean#L19-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IsChowFormCMul
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

theorem P2M_GroundTheory_Heights__Heights_Vertical_specFirst_C_mul_fbe46aaee29f {R : Type*} [CommSemiring R] {n k : ℕ} (c : R)
    (f : MvPolynomial (Fin (k + 1) × Fin n) R) (u : Fin n → R) :
    specFirst (C c * f) u = C c * specFirst f u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«specFirst_C_mul» := P2M_GroundTheory_Heights__Heights_Vertical_specFirst_C_mul_fbe46aaee29f
