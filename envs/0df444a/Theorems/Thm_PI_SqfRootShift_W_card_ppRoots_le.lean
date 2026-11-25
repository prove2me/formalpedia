-- Prove2me | Theorems.Thm_PI_SqfRootShift_W_card_ppRoots_le
-- name    : PI.SqfRootShift.W.card_ppRoots_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:26:47.293855+00:00
-- url     : https://prove2.me/theorems/17f6e31f-c842-484c-b4cc-c4d4f7fb6c68
-- title:
--   W: card pp Roots le
-- statement:
--   The W construction uses the card pp Roots le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/CountA.lean#L47-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/CountA.lean#L47-L78

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootShift PI.SqfRootShift.W
open PI.SqfLab
open Classical

theorem PI.SqfRootShift.W.card_ppRoots_le {K : Type*} [Field K] (N : ℕ) (hN : 2 ≤ N) :
    ((Polynomial.nthRootsFinset N (1 : K)).filter
      (fun y => ∃ ℓ, ℓ.Prime ∧ ∃ j, y ^ (ℓ ^ j) = 1)).card ≤ ppSum N := by sorry
