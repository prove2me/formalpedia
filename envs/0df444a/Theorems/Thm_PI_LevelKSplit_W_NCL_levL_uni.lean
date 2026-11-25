-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCL_levL_uni
-- name    : PI.LevelKSplit.W.NCL.levL_uni
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:36:43.585697+00:00
-- url     : https://prove2.me/theorems/231a3591-12fd-5f1d-ade5-0c8c87781b55
-- title:
--   NCL: lev L uni
-- statement:
--   The NCL construction uses the lev L uni property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevLSubPerp.lean#L210-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevLSubPerp.lean#L210-L216

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

theorem PI.LevelKSplit.W.NCL.levL_uni (H : D.Hyp) (U W : Matrix (Fin r) (Fin r) A)
    (hUW : ∀ b c, ∑ a, D.σA (U a b) * W a c = if b = c then 1 else 0)
    (hWU : ∀ b c, ∑ a, D.σA (W a b) * U a c = if b = c then 1 else 0) (x y : n → A) :
    D.h (levL D U W x) (levL D U W y) = D.h x y := by sorry
