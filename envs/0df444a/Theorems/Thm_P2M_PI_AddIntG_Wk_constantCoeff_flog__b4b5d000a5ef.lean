-- Prove2me | Theorems.Thm_P2M_PI_AddIntG_Wk_constantCoeff_flog__b4b5d000a5ef
-- name    : P2M_PI_AddIntG_Wk_constantCoeff_flog__b4b5d000a5ef
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:55:35.913631+00:00
-- url     : https://prove2.me/theorems/dee238ee-ef96-489a-aaf5-5b319958e7f7
-- title:
--   P2 M PI Add Int G Wk constant Coeff flog  b4b5d000a5ef: P2 M PI Add Int G Wk constant Coeff flog  b4b5d000a5ef
-- statement:
--   The P2 M PI Add Int G Wk constant Coeff flog  b4b5d000a5ef construction uses the P2 M PI Add Int G Wk constant Coeff flog  b4b5d000a5ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/FormalGroupLawExists.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/FormalGroupLawExists.lean#L34-L38

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_VarZeroSubVarOneNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]

theorem P2M_PI_AddIntG_Wk_constantCoeff_flog__b4b5d000a5ef (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (flog W wq) = 0 := by sorry

alias «PI».«AddIntG».«Wk».«constantCoeff_flog'» := P2M_PI_AddIntG_Wk_constantCoeff_flog__b4b5d000a5ef
