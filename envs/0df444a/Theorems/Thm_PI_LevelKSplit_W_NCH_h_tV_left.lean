-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCH_h_tV_left
-- name    : PI.LevelKSplit.W.NCH.h_tV_left
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:35:24.884263+00:00
-- url     : https://prove2.me/theorems/2f8b87f1-1b03-51c7-b366-ddef9f7435ff
-- title:
--   NCH: h t V left
-- statement:
--   The NCH construction uses the h t V left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/UnipotentRadicalActionFormula.lean#L218-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/UnipotentRadicalActionFormula.lean#L218-L223

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

theorem PI.LevelKSplit.W.NCH.h_tV_left (x x' : n → A) :
    D.h (tV D half y x) x' = ∑ a, D.σA (D.h (D.e a) x) * D.h (y a) x' +
      ∑ a, ∑ b, D.σA (D.h (D.e a) x) * (D.σA (cf D half y a b) * D.h (D.e b) x') -
      ∑ b, D.σA (D.h (y b) x) * D.h (D.e b) x' := by sorry
