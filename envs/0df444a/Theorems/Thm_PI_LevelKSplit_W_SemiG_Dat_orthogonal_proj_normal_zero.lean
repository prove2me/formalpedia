-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_orthogonal_proj_normal_zero
-- name    : PI.LevelKSplit.W.SemiG.Dat.orthogonal_proj_normal_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:37:21.162217+00:00
-- url     : https://prove2.me/theorems/88a378fc-c1a9-5f30-b8e1-1e27b58d0163
-- title:
--   Dat: orthogonal proj normal zero
-- statement:
--   The Dat construction uses the orthogonal proj normal zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiGen.lean#L189-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiGen.lean#L189-L190

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

theorem PI.LevelKSplit.W.SemiG.Dat.orthogonal_proj_normal_zero (H : D.Hyp) : D.pW D.z = 0 := by sorry
