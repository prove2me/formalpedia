-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCH_h_tV_tV
-- name    : PI.LevelKSplit.W.NCH.h_tV_tV
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:34:14.717644+00:00
-- url     : https://prove2.me/theorems/61361834-0f53-4697-8687-9758cda91d58
-- title:
--   NCH: h t V t V
-- statement:
--   The NCH construction uses the h t V t V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/UnipotentRadicalActionFormula.lean#L225-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/UnipotentRadicalActionFormula.lean#L225-L237

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCH
open PI.VolSemiDirect.W.PG PI.VolSemiDirect.W.PG.Dat
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
variable {D : Dat A n r}
variable (H : D.Hyp) {half : A} {y : Fin r → n → A} (hy : ∀ a, IsWp D (y a))
include H hy

theorem PI.LevelKSplit.W.NCH.h_tV_tV (x x' : n → A) :
    D.h (tV D half y x) (tV D half y x') =
      ∑ a, ∑ b, D.σA (D.h (D.e a) x) * (D.h (D.e b) x' * D.h (y a) (y b)) := by sorry
