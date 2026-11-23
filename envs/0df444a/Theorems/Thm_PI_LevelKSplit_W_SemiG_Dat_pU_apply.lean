-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pU_apply
-- name    : PI.LevelKSplit.W.SemiG.Dat.pU_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:12:10.812763+00:00
-- url     : https://prove2.me/theorems/6b1107a3-236a-4429-b9b7-45fc36ff35d8
-- title:
--   Dat: p U apply
-- statement:
--   The Dat construction uses the p U apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiGen.lean#L120-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiGen.lean#L120-L120

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

theorem PI.LevelKSplit.W.SemiG.Dat.pU_apply (v : n → A) : D.pU v = D.pX v + D.pXv v + D.pz v := by sorry
