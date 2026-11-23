-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_Loc_dl_apply
-- name    : PI.LevelKSplit.W.Loc.dl_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:32:50.485208+00:00
-- url     : https://prove2.me/theorems/e343c153-97cb-49d6-a61f-45373cd64f43
-- title:
--   Loc: dl apply
-- statement:
--   The Loc construction uses the dl apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/MulVecSpanStable.lean#L14-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/MulVecSpanStable.lean#L14-L14

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

theorem PI.LevelKSplit.W.Loc.dl_apply (c y : Fin n → B) : dl c y = c ⬝ᵥ y := by sorry
