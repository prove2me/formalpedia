-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qk46_le_iff_lt_colH
-- name    : UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:19:49.112804+00:00
-- url     : https://prove2.me/theorems/43cda7a0-7125-46f8-ac4a-054de3bca6aa
-- title:
--   Qk46: le iff lt col H
-- statement:
--   The Qk46 construction uses the le iff lt col H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/LeIffLtColH.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/LeIffLtColH.lean#L7-L21

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeIffLtColH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH :
    ∀ {r : Nat} {μ : Fin r → Int},
      @Antitone (Fin r) Int (@PartialOrder.toPreorder (Fin r) (@Fin.instPartialOrder r))
          (@PartialOrder.toPreorder Int
            (@ConditionallyCompletePartialOrderSup.toPartialOrder Int
              (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup Int
                (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder Int
                  (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice Int
                    Int.instConditionallyCompleteLinearOrder)))))
          μ →
        ∀ (c : Int) (m : Fin r),
          Iff (@LE.le Int Int.instLEInt c (μ m)) (@LT.lt Nat instLTNat (@Fin.val r m) (@UpperTheory.Reformulated.B.Qk46.colH r μ c)) := by sorry
