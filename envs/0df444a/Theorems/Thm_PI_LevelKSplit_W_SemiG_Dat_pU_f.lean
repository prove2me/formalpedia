-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pU_f
-- name    : PI.LevelKSplit.W.SemiG.Dat.pU_f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:32:54.597117+00:00
-- url     : https://prove2.me/theorems/6f60fbba-a902-4ee6-9b23-aebcea80b4e5
-- title:
--   Dat: p U f
-- statement:
--   The Dat construction uses the p U f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiGen.lean#L175-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiGen.lean#L175-L177

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

theorem PI.LevelKSplit.W.SemiG.Dat.pU_f (H : D.Hyp) (b : Fin r) : D.pU (D.f b) = D.f b := by sorry
