-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pW_of_isW
-- name    : PI.LevelKSplit.W.SemiG.Dat.pW_of_isW
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:34:44.364185+00:00
-- url     : https://prove2.me/theorems/12d3ed5e-5b7b-40df-9f1e-2bac4928dfa7
-- title:
--   Dat: p W of is W
-- statement:
--   The Dat construction uses the p W of is W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiGen.lean#L156-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiGen.lean#L156-L157

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.LevelKSplit.W.SemiG.Dat
variable (D : Dat A n r)
variable {D}
variable (D)
variable {D}

theorem PI.LevelKSplit.W.SemiG.Dat.pW_of_isW {w : n → A} (hw : IsW D w) : D.pW w = w := by sorry
