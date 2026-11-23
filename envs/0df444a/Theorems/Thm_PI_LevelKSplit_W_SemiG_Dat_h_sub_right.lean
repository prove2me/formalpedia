-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_sub_right
-- name    : PI.LevelKSplit.W.SemiG.Dat.h_sub_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:37:54.298203+00:00
-- url     : https://prove2.me/theorems/d583f9d1-ea59-4d3d-9578-e0ed2f0aefb1
-- title:
--   Dat: h sub right
-- statement:
--   The Dat construction uses the h sub right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiGen.lean#L40-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiGen.lean#L40-L40

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

theorem PI.LevelKSplit.W.SemiG.Dat.h_sub_right (x y y' : n → A) : D.h x (y - y') = D.h x y - D.h x y' := by sorry
