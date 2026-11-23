-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_rlen_map
-- name    : PI.IsoDetW.Loc.rlen_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:10.726989+00:00
-- url     : https://prove2.me/theorems/1610a768-46b5-4127-9b15-c087f97cc1b0
-- title:
--   Loc: rlen map
-- statement:
--   The Loc construction uses the rlen map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LidxAntisymm.lean#L73-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LidxAntisymm.lean#L73-L91

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

theorem PI.IsoDetW.Loc.rlen_map {W' : Type*} [AddCommGroup W'] [Module R W'] (f : W →ₗ[R] W')
    (hf : Function.Injective f) (X Z : Submodule R W) :
    relative₂ (X.map f) (Z.map f) = relative₂ X Z := by sorry
