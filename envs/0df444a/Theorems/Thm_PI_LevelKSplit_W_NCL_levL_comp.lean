-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCL_levL_comp
-- name    : PI.LevelKSplit.W.NCL.levL_comp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:36:36.972718+00:00
-- url     : https://prove2.me/theorems/4e4de028-df50-42a2-882d-6c3789761ba2
-- title:
--   NCL: lev L comp
-- statement:
--   The NCL construction uses the lev L comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevLSubPerp.lean#L126-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevLSubPerp.lean#L126-L135

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

theorem PI.LevelKSplit.W.NCL.levL_comp (U W U' W' : Matrix (Fin r) (Fin r) A) (x : n → A) :
    levL D U W (levL D U' W' x) = levL D (U * U') (W * W') x := by sorry
