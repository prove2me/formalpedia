-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCL_h_f_pXv
-- name    : PI.LevelKSplit.W.NCL.h_f_pXv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:34:46.000715+00:00
-- url     : https://prove2.me/theorems/985aa65a-8feb-48bf-8a13-7f49392b9b08
-- title:
--   NCL: h f p Xv
-- statement:
--   The NCL construction uses the h f p Xv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevLSubPerp.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevLSubPerp.lean#L83-L85

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

theorem PI.LevelKSplit.W.NCL.h_f_pXv (c : Fin r) (x : n → A) : D.h (D.f c) (D.pXv x) = 0 := by sorry
