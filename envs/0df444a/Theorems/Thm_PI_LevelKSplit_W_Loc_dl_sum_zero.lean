-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_Loc_dl_sum_zero
-- name    : PI.LevelKSplit.W.Loc.dl_sum_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:46:21.880821+00:00
-- url     : https://prove2.me/theorems/a041239b-bb77-47ce-badd-e12143b11743
-- title:
--   Loc: dl sum zero
-- statement:
--   The Loc construction uses the dl sum zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/MulVecSpanStable.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/MulVecSpanStable.lean#L22-L24

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulVecSpanStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.Loc
open Submodule
variable {O B : Type} [CommRing O] [CommRing B] [Algebra O B] {n r : ℕ}
omit [CommRing O] [Algebra O B]

theorem PI.LevelKSplit.W.Loc.dl_sum_zero (c : Fin n → B) (v : Fin r → Fin n → B) (d : Fin r → B)
    (h : ∀ a, c ⬝ᵥ v a = 0) : dl c (∑ a, d a • v a) = 0 := by sorry
