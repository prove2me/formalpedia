-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_lidx_eq
-- name    : PI.IsoDetW.Loc.lidx_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:27:23.32432+00:00
-- url     : https://prove2.me/theorems/9b10f0f2-76e0-42e0-aebc-d5f2d48e2681
-- title:
--   Loc: lidx eq
-- statement:
--   The Loc construction uses the lidx eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LidxAntisymm.lean#L109-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LidxAntisymm.lean#L109-L111

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

theorem PI.IsoDetW.Loc.lidx_eq (A B : Submodule R W) :
    lidx p A B = ((relative₂ (localization₂ p (A ⊓ B)) (localization₂ p A)).toNat : ℤ) - (relative₂ (localization₂ p (A ⊓ B)) (localization₂ p B)).toNat := by sorry
