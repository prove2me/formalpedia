-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_BoxBounds_exists_box_le
-- name    : UpperTheory.Reformulated.B.BoxBounds.exists_box_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:12:23.238219+00:00
-- url     : https://prove2.me/theorems/d95491cc-5f97-43d5-a9bd-3fcf7252eb12
-- title:
--   Box Bounds: exists box le
-- statement:
--   The Box Bounds construction uses the exists box le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/BoxBounds.lean#L7-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/BoxBounds.lean#L7-L40

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BoxBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.BoxBounds.exists_box_le :
    ∀ {K : Type} [inst : Field K] [NumberField K] {i : ℕ} (L : Submodule (NumberField.RingOfIntegers K) (Fin i → K)),
      Submodule.span K (↑L : Set (Fin i → K)) = ⊤ →
        ∃ (e : NumberField.RingOfIntegers K),
          e ≠ (0 : NumberField.RingOfIntegers K) ∧
            UpperTheory.Reformulated.B.BoxBounds.box
                ((Algebra.algebraMap (NumberField.RingOfIntegers K) K : NumberField.RingOfIntegers K → K) e) ≤
              L := by sorry
