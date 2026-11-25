-- Prove2me | Theorems.Thm_PI_WSF_cz_diag_unitary
-- name    : PI.WSF.cz_diag_unitary
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:45:34.162571+00:00
-- url     : https://prove2.me/theorems/3c64d6c4-e4a0-50cd-9701-95eab4c9d967
-- title:
--   WSF: cz diag unitary
-- statement:
--   The WSF construction uses the cz diag unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/CzDiagUnitary.lean#L48-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/CzDiagUnitary.lean#L48-L56

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CzDiagUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WSF
open MvPolynomial Matrix
open scoped ComplexOrder

theorem PI.WSF.cz_diag_unitary {N : ℕ} (z : Fin N → ℂ) (hz : ∀ i, ‖z i‖ = 1) :
    diagonal z ∈ unitaryGroup (Fin N) ℂ := by sorry
