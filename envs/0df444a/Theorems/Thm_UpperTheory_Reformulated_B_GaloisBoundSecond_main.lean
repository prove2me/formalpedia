-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_GaloisBoundSecond_main
-- name    : UpperTheory.Reformulated.B.GaloisBoundSecond.main
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:12:24.802546+00:00
-- url     : https://prove2.me/theorems/6a6c6a00-5a12-4068-9672-6c66ddcce5f3
-- title:
--   Galois Bound Second: main
-- statement:
--   The Galois Bound Second construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/GaloisBoundSecond.lean#L167-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/GaloisBoundSecond.lean#L167-L186

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GaloisBoundSecond
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField

theorem UpperTheory.Reformulated.B.GaloisBoundSecond.main :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] [NumberField.IsTotallyReal F] (N : ℕ),
      (0 : ℕ) < N →
        ∀ (I : Ideal (NumberField.RingOfIntegers F)),
          I ≠ ⊥ →
            ∀ (B : ℝ),
              (0 : ℝ) ≤ B →
                {x : F |
                      x ≠ (0 : F) ∧
                        (∃ y ∈ I, (↑y : F) = (↑N : F) * x) ∧
                          ∀ (w : NumberField.InfinitePlace F), (w : F → ℝ) x ≤ B}.Finite ∧
                  (↑{x : F |
                              x ≠ (0 : F) ∧
                                (∃ y ∈ I, (↑y : F) = (↑N : F) * x) ∧
                                  ∀ (w : NumberField.InfinitePlace F), (w : F → ℝ) x ≤ B}.ncard :
                        ℝ) *
                      (↑((Ideal.absNorm : Ideal (NumberField.RingOfIntegers F) → ℕ) I) : ℝ) ≤
                    ((4 : ℝ) * B * (↑N : ℝ)) ^ Module.finrank ℚ F := by sorry
