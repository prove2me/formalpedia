-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_IntegerDenominator_exists_denom_pt
-- name    : UpperTheory.Reformulated.B.IntegerDenominator.exists_denom_pt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:45:48.9414+00:00
-- url     : https://prove2.me/theorems/73b549c8-f3eb-406c-8a31-f6e9df86c986
-- title:
--   Integer Denominator: exists denom pt
-- statement:
--   The Integer Denominator construction uses the exists denom pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntegerDenominator.lean#L31-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntegerDenominator.lean#L31-L48

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegerDenominator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.IntegerDenominator.exists_denom_pt :
    ∀ {F E : Type} [inst : Field F] [NumberField F] [inst_2 : Field E]
    [NumberField E] [inst_4 : Algebra F E] {n : Type} [Fintype n] [DecidableEq n]
    (L : Submodule (NumberField.RingOfIntegers E) (n → E)),
    Submodule.span E (↑L : Set (n → E)) = ⊤ →
      ∀ (x : n → E),
        ∃ (D : NumberField.RingOfIntegers F),
          D ≠ (0 : NumberField.RingOfIntegers F) ∧ (Algebra.algebraMap F E : F → E) (↑D : F) • x ∈ L := by sorry
