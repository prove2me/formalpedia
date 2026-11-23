-- Prove2me | Theorems.Thm_P2M_PI_LevelKSplit_W_NCH_h_W_e__02b956afd230
-- name    : P2M_PI_LevelKSplit_W_NCH_h_W_e__02b956afd230
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:30:06.25382+00:00
-- url     : https://prove2.me/theorems/e28eea25-39c6-4845-923a-62612f361338
-- title:
--   P2 M PI Level KSplit W NCH h W e  02b956afd230: P2 M PI Level KSplit W NCH h W e  02b956afd230
-- statement:
--   The P2 M PI Level KSplit W NCH h W e  02b956afd230 construction uses the P2 M PI Level KSplit W NCH h W e  02b956afd230 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/UnipotentRadicalActionFormula.lean#L96-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/UnipotentRadicalActionFormula.lean#L96-L98

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCH
open PI.VolSemiDirect.W.PG PI.VolSemiDirect.W.PG.Dat
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
variable {D : Dat A n r}

theorem P2M_PI_LevelKSplit_W_NCH_h_W_e__02b956afd230 (H : D.Hyp) {w : n → A} (hw : IsWp D w) (b : Fin r) : D.h w (D.e b) = 0 := by sorry

alias «PI».«LevelKSplit».«W».«NCH».«h_W_e'» := P2M_PI_LevelKSplit_W_NCH_h_W_e__02b956afd230
