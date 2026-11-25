-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCL_h_f_levL
-- name    : PI.LevelKSplit.W.NCL.h_f_levL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:28:05.622977+00:00
-- url     : https://prove2.me/theorems/7fcbd10a-43fa-478a-967c-c24d810c8254
-- title:
--   NCL: h f lev L
-- statement:
--   The NCL construction uses the h f lev L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevLSubPerp.lean#L103-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevLSubPerp.lean#L103-L106

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

theorem PI.LevelKSplit.W.NCL.h_f_levL (U W : Matrix (Fin r) (Fin r) A) (c : Fin r) (x : n → A) :
    D.h (D.f c) (levL D U W x) = ∑ b, U c b * D.h (D.f b) x := by sorry
