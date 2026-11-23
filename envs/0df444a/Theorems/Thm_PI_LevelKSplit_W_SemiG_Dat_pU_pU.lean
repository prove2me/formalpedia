-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pU_pU
-- name    : PI.LevelKSplit.W.SemiG.Dat.pU_pU
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:16:56.329565+00:00
-- url     : https://prove2.me/theorems/f3c99c7e-0025-4a0f-8010-2cd1763a3625
-- title:
--   Dat: p U p U
-- statement:
--   The Dat construction uses the p U p U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiGen.lean#L159-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiGen.lean#L159-L162

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

theorem PI.LevelKSplit.W.SemiG.Dat.pU_pU (H : D.Hyp) (v : n → A) : D.pU (D.pU v) = D.pU v := by sorry
