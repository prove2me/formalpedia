-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCL_h_decomp
-- name    : PI.LevelKSplit.W.NCL.h_decomp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:36:37.472979+00:00
-- url     : https://prove2.me/theorems/b130531d-b31e-5620-b4b9-08c7981748e3
-- title:
--   NCL: h decomp
-- statement:
--   The NCL construction uses the h decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevLSubPerp.lean#L180-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevLSubPerp.lean#L180-L190

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

theorem PI.LevelKSplit.W.NCL.h_decomp (x y : n → A) :
    D.h x y = D.h (pV D x) (pV D y) + ∑ a, D.σA (D.h (D.f a) x) * D.h (D.e a) y +
      ∑ a, D.σA (D.h (D.e a) x) * D.h (D.f a) y := by sorry
