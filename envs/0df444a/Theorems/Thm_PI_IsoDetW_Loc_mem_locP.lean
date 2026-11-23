-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_mem_locP
-- name    : PI.IsoDetW.Loc.mem_locP
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:09.995325+00:00
-- url     : https://prove2.me/theorems/809d5283-42a8-4607-911b-388ca0ae7b4c
-- title:
--   Loc: mem loc P
-- statement:
--   The Loc construction uses the mem loc P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LidxAntisymm.lean#L100-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LidxAntisymm.lean#L100-L101

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoDetW PI.IsoDetW.Loc
open PI.IsoDetDefs
variable {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W] [Module R W]
variable (p : Ideal R) [p.IsPrime]

theorem PI.IsoDetW.Loc.mem_locP {A : Submodule R W} {x : W} :
    x ∈ localization₂ p A ↔ ∃ s ∈ p.primeCompl, s • x ∈ A := by sorry
