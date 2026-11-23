-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Ybf4_isIntegral_det
-- name    : UpperTheory.Reformulated.B.Ybf4.isIntegral_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:46.303233+00:00
-- url     : https://prove2.me/theorems/7c8e4f26-ff47-40c3-8661-c8d57c917160
-- title:
--   Ybf4: is Integral det
-- statement:
--   The Ybf4 construction uses the is Integral det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IsIntegralDetOfIsIntegral.lean#L28-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IsIntegralDetOfIsIntegral.lean#L28-L69

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsIntegralDetOfIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open Polynomial

theorem UpperTheory.Reformulated.B.Ybf4.isIntegral_det :
    ∀ {E : Type} [inst : Field E] [NumberField E] {N : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin N → E)),
      L.FG →
        Submodule.span E (↑L : Set (Fin N → E)) = ⊤ →
          ∀ (γ : Matrix (Fin N) (Fin N) E), (∀ v ∈ L, γ.mulVec v ∈ L) → IsIntegral ℤ γ.det := by sorry
