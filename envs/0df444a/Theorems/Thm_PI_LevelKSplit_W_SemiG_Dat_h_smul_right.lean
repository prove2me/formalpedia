-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_smul_right
-- name    : PI.LevelKSplit.W.SemiG.Dat.h_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:14:47.412285+00:00
-- url     : https://prove2.me/theorems/7884d645-977d-4cf2-897e-bc766189b6a2
-- title:
--   Dat: h smul right
-- statement:
--   The Dat construction uses the h smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiGen.lean#L38-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiGen.lean#L38-L38

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

theorem PI.LevelKSplit.W.SemiG.Dat.h_smul_right (x y : n → A) (c : A) : D.h x (c • y) = c * D.h x y := by sorry
