-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCL_h_e_pV
-- name    : PI.LevelKSplit.W.NCL.h_e_pV
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:27:48.165859+00:00
-- url     : https://prove2.me/theorems/f8490f24-8733-42f5-884f-b2ca2f66f99a
-- title:
--   NCL: h e p V
-- statement:
--   The NCL construction uses the h e p V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevLSubPerp.lean#L99-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevLSubPerp.lean#L99-L101

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

theorem PI.LevelKSplit.W.NCL.h_e_pV (c : Fin r) (x : n → A) : D.h (D.e c) (pV D x) = 0 := by sorry
