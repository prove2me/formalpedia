-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_FiniteAndNcardBound_finite_and_ncard_le
-- name    : UpperTheory.Reformulated.B.FiniteAndNcardBound.finite_and_ncard_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:23.359329+00:00
-- url     : https://prove2.me/theorems/503175d8-3ebf-4616-bb31-04f3e5aad5eb
-- title:
--   Finite And Ncard Bound: finite and ncard le
-- statement:
--   The Finite And Ncard Bound construction uses the finite and ncard le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FiniteAndNcardBound.lean#L4-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FiniteAndNcardBound.lean#L4-L64

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FiniteAndNcardBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open NumberField

theorem UpperTheory.Reformulated.B.FiniteAndNcardBound.finite_and_ncard_le :
    ∀ (E : Type) [inst : Field E] [NumberField E],
    ∃ (C : ℝ) (N : ℕ),
      ∀ (R : ℝ),
        (1 : ℝ) ≤ R →
          {r : NumberField.RingOfIntegers E | ∀ (w : NumberField.InfinitePlace E), (w : E → ℝ) (↑r : E) ≤ R}.Finite ∧
            (↑{r : NumberField.RingOfIntegers E | ∀ (w : NumberField.InfinitePlace E), (w : E → ℝ) (↑r : E) ≤ R}.ncard :
                ℝ) ≤
              C * R ^ N := by sorry
