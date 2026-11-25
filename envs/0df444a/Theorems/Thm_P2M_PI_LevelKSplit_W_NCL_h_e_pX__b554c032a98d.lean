-- Prove2me | Theorems.Thm_P2M_PI_LevelKSplit_W_NCL_h_e_pX__b554c032a98d
-- name    : P2M_PI_LevelKSplit_W_NCL_h_e_pX__b554c032a98d
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:57:02.17437+00:00
-- url     : https://prove2.me/theorems/6482ecad-3c4b-44c2-97ce-33e4c62f8e62
-- title:
--   P2 M PI Level KSplit W NCL h e p X  b554c032a98d: P2 M PI Level KSplit W NCL h e p X  b554c032a98d
-- statement:
--   The P2 M PI Level KSplit W NCL h e p X  b554c032a98d construction uses the P2 M PI Level KSplit W NCL h e p X  b554c032a98d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevLSubPerp.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevLSubPerp.lean#L87-L89

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCL
open PI.VolSemiDirect.W.PG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
variable {D : Dat A n r}
variable (H : D.Hyp)
include H

theorem P2M_PI_LevelKSplit_W_NCL_h_e_pX__b554c032a98d (c : Fin r) (x : n → A) : D.h (D.e c) (D.pX x) = 0 := by sorry

alias «PI».«LevelKSplit».«W».«NCL».«h_e_pX'» := P2M_PI_LevelKSplit_W_NCL_h_e_pX__b554c032a98d
