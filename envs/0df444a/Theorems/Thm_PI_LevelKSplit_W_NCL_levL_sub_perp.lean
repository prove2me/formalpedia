-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCL_levL_sub_perp
-- name    : PI.LevelKSplit.W.NCL.levL_sub_perp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:34:28.186478+00:00
-- url     : https://prove2.me/theorems/661cbf0e-d9e0-4128-811f-da012ecfc6bb
-- title:
--   NCL: lev L sub perp
-- statement:
--   The NCL construction uses the lev L sub perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevLSubPerp.lean#L162-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevLSubPerp.lean#L162-L172

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCL
open PI.VolSemiDirect.W.PG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
variable {D : Dat A n r}
variable (H : D.Hyp)
include H

theorem PI.LevelKSplit.W.NCL.levL_sub_perp (U W : Matrix (Fin r) (Fin r) A) {v : n → A} (he : ∀ b, D.h (D.e b) v = 0) :
    levL D U W v - v ∈ Submodule.span A (Set.range D.e) := by sorry
