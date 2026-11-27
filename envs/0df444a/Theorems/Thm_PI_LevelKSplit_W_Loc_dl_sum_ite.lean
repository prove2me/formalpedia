-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_Loc_dl_sum_ite
-- name    : PI.LevelKSplit.W.Loc.dl_sum_ite
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:46:12.052468+00:00
-- url     : https://prove2.me/theorems/bf71f818-6031-4286-8614-554540d98213
-- title:
--   Loc: dl sum ite
-- statement:
--   The Loc construction uses the dl sum ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/MulVecSpanStable.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/MulVecSpanStable.lean#L17-L19

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

theorem PI.LevelKSplit.W.Loc.dl_sum_ite (c : Fin n → B) (v : Fin r → Fin n → B) (d : Fin r → B) (b : Fin r)
    (h : ∀ a, c ⬝ᵥ v a = if a = b then 1 else 0) : dl c (∑ a, d a • v a) = d b := by sorry
