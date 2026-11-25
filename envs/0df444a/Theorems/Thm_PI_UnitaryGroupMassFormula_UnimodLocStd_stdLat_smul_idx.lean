-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_stdLat_smul_idx
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.stdLat_smul_idx
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:44:41.534413+00:00
-- url     : https://prove2.me/theorems/3261e80d-28d7-4e82-987c-c31f2c050da9
-- title:
--   Unimod Loc Std: std Lat smul idx
-- statement:
--   The Unimod Loc Std construction uses the std Lat smul idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RelIdxNeZeroOfLeLeft.lean#L119-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RelIdxNeZeroOfLeLeft.lean#L119-L164

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RelIdxNeZeroOfLeLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.stdLat_smul_idx (L : PeriodPair) (m : Type*) [Fintype m] {N : ℕ} (hN : N ≠ 0) :
    ((stdLat L m).map (smulHom (N : ℂ))).relIndex (stdLat L m) ≠ 0 := by sorry
