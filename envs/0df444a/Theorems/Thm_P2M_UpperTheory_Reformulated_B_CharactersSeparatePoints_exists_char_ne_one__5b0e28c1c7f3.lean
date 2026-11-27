-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_CharactersSeparatePoints_exists_char_ne_one__5b0e28c1c7f3
-- name    : P2M_UpperTheory_Reformulated_B_CharactersSeparatePoints_exists_char_ne_one__5b0e28c1c7f3
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:43:47.758872+00:00
-- url     : https://prove2.me/theorems/43e9cf7b-6da0-45c8-ab29-ad63b4a7e289
-- title:
--   P2 M Upper Theory Reformulated B Characters Separate Points exists char ne one  5b0e28c1c7f3: P2 M Upper Theory Reformulated B Characters Separate Points exists char ne one  5b0e28c1c7f3
-- statement:
--   The P2 M Upper Theory Reformulated B Characters Separate Points exists char ne one  5b0e28c1c7f3 construction uses the P2 M Upper Theory Reformulated B Characters Separate Points exists char ne one  5b0e28c1c7f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsCharNeOne.lean#L182-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsCharNeOne.lean#L182-L228

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsCharNeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory WeakDual

theorem P2M_UpperTheory_Reformulated_B_CharactersSeparatePoints_exists_char_ne_one__5b0e28c1c7f3.{u_1} :
    ∀ {C : Type u_1} [inst : CommGroup C] [inst_1 : TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C] [T2Space C]
      {g : C}, g ≠ (1 : C) → ∃ (χ : C →ₜ* Circle), (χ : C → Circle) g ≠ (1 : Circle) := by sorry

alias «UpperTheory».«Reformulated».«B».«CharactersSeparatePoints».«exists_char_ne_one».«» := P2M_UpperTheory_Reformulated_B_CharactersSeparatePoints_exists_char_ne_one__5b0e28c1c7f3
