-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_f_pU
-- name    : PI.LevelKSplit.W.SemiG.Dat.h_f_pU
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:32:55.135801+00:00
-- url     : https://prove2.me/theorems/9df5ea0b-4596-4643-9b5f-b1687761ed67
-- title:
--   Dat: h f p U
-- statement:
--   The Dat construction uses the h f p U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiGen.lean#L133-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiGen.lean#L133-L135

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

theorem PI.LevelKSplit.W.SemiG.Dat.h_f_pU (H : D.Hyp) (a : Fin r) (v : n → A) : D.h (D.f a) (D.pU v) = D.h (D.f a) v := by sorry
