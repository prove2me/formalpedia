-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_lidx_eq_of_le
-- name    : PI.IsoDetW.Loc.lidx_eq_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:35.313387+00:00
-- url     : https://prove2.me/theorems/f2950445-453a-4678-84a1-147ecfb5c012
-- title:
--   Loc: lidx eq of le
-- statement:
--   The Loc construction uses the lidx eq of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LidxAntisymm.lean#L119-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LidxAntisymm.lean#L119-L131

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

theorem PI.IsoDetW.Loc.lidx_eq_of_le {A B D : Submodule R W} (hD : D ≤ A ⊓ B)
    (hA : relative₂ (localization₂ p D) (localization₂ p A) ≠ ⊤) (hB : relative₂ (localization₂ p D) (localization₂ p B) ≠ ⊤) :
    lidx p A B = ((relative₂ (localization₂ p D) (localization₂ p A)).toNat : ℤ) - (relative₂ (localization₂ p D) (localization₂ p B)).toNat := by sorry
