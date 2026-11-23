-- Prove2me | Theorems.Thm_P2M_PI_IsoDetW_Loc_localization_map__da8ebf0c7662
-- name    : P2M_PI_IsoDetW_Loc_localization_map__da8ebf0c7662
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:11.425715+00:00
-- url     : https://prove2.me/theorems/163a322e-771f-4c47-a6c5-594bb4c75e0a
-- title:
--   P2 M PI Iso Det W Loc localization map  da8ebf0c7662: P2 M PI Iso Det W Loc localization map  da8ebf0c7662
-- statement:
--   The P2 M PI Iso Det W Loc localization map  da8ebf0c7662 construction uses the P2 M PI Iso Det W Loc localization map  da8ebf0c7662 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LidxAntisymm.lean#L141-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LidxAntisymm.lean#L141-L154

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

theorem P2M_PI_IsoDetW_Loc_localization_map__da8ebf0c7662 {W' : Type*} [AddCommGroup W'] [Module R W'] (f : W →ₗ[R] W')
    (hf : Function.Injective f)
    (hsat : ∀ (s : R) (y : W'), s ∈ p.primeCompl → s • y ∈ LinearMap.range f → y ∈ LinearMap.range f)
    (A : Submodule R W) : localization₂ p (A.map f) = (localization₂ p A).map f := by sorry

alias «PI».«IsoDetW».«Loc».«localization_map₂» := P2M_PI_IsoDetW_Loc_localization_map__da8ebf0c7662
