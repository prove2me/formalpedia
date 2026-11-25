-- Prove2me | Theorems.Thm_P2M_PI_LevelKSplit_W_NCH_h_W_span__a0509f779950
-- name    : P2M_PI_LevelKSplit_W_NCH_h_W_span__a0509f779950
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:57:12.509148+00:00
-- url     : https://prove2.me/theorems/8ad20b4d-069f-44c5-95b5-5203bd902c61
-- title:
--   P2 M PI Level KSplit W NCH h W span  a0509f779950: P2 M PI Level KSplit W NCH h W span  a0509f779950
-- statement:
--   The P2 M PI Level KSplit W NCH h W span  a0509f779950 construction uses the P2 M PI Level KSplit W NCH h W span  a0509f779950 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/UnipotentRadicalActionFormula.lean#L110-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/UnipotentRadicalActionFormula.lean#L110-L114

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

theorem P2M_PI_LevelKSplit_W_NCH_h_W_span__a0509f779950 (H : D.Hyp) {w : n → A} (hw : IsWp D w) {x : n → A}
    (hx : x ∈ Submodule.span A (Set.range D.e)) : D.h w x = 0 := by sorry

alias «PI».«LevelKSplit».«W».«NCH».«h_W_span'» := P2M_PI_LevelKSplit_W_NCH_h_W_span__a0509f779950
