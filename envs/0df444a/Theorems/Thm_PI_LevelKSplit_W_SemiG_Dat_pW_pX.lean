-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pW_pX
-- name    : PI.LevelKSplit.W.SemiG.Dat.pW_pX
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:46:05.946975+00:00
-- url     : https://prove2.me/theorems/12ef0395-02dd-5459-9451-bb283154c656
-- title:
--   Dat: p W p X
-- statement:
--   The Dat construction uses the p W p X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiGen.lean#L192-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiGen.lean#L192-L194

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

theorem PI.LevelKSplit.W.SemiG.Dat.pW_pX (H : D.Hyp) (u : n → A) : D.pW (D.pX u) = 0 := by sorry
