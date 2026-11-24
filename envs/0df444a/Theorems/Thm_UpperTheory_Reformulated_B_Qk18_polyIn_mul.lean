-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qk18_polyIn_mul
-- name    : UpperTheory.Reformulated.B.Qk18.polyIn_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:23.09481+00:00
-- url     : https://prove2.me/theorems/0231b09f-1c05-4527-b1af-1ae76e45f386
-- title:
--   Qk18: poly In mul
-- statement:
--   The Qk18 construction uses the poly In mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/PolyInMul.lean#L8-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/PolyInMul.lean#L8-L31

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PolyInMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qk18.polyIn_mul :
    ∀ {R : Type} [inst : Ring R] [inst_1 : Algebra ℂ R] {f g : ℂ → R} {d₁ d₂ : ℕ},
      UpperTheory.Reformulated.B.Qk18.PolyIn f d₁ →
        UpperTheory.Reformulated.B.Qk18.PolyIn g d₂ → UpperTheory.Reformulated.B.Qk18.PolyIn (fun (t : ℂ) ↦ f t * g t) (d₁ + d₂) := by sorry
