-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pz_apply
-- name    : PI.LevelKSplit.W.SemiG.Dat.pz_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:12:36.88683+00:00
-- url     : https://prove2.me/theorems/c90c30f3-7439-4681-8798-2cf0cba2cfac
-- title:
--   Dat: pz apply
-- statement:
--   The Dat construction uses the pz apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiGen.lean#L117-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiGen.lean#L117-L118

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

theorem PI.LevelKSplit.W.SemiG.Dat.pz_apply (v : n → A) : D.pz v = (D.tz * D.h D.z v) • D.z := by sorry
