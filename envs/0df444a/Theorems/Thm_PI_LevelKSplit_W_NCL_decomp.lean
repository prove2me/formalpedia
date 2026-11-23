-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCL_decomp
-- name    : PI.LevelKSplit.W.NCL.decomp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:28:26.056141+00:00
-- url     : https://prove2.me/theorems/56fb14d0-1b79-4852-a011-c85d012b6ae9
-- title:
--   NCL: decomp
-- statement:
--   The NCL construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevLSubPerp.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevLSubPerp.lean#L58-L60

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

theorem PI.LevelKSplit.W.NCL.decomp (D : Dat A n r) (x : n → A) : x = pV D x + D.pX x + D.pXv x := by sorry
