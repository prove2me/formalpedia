-- Prove2me | Theorems.Thm_PI_WSF_cz_zariski
-- name    : PI.WSF.cz_zariski
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:45:40.155349+00:00
-- url     : https://prove2.me/theorems/03b84b7a-fd60-5683-9270-e5b41e846599
-- title:
--   WSF: cz zariski
-- statement:
--   The WSF construction uses the cz zariski property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/CzDiagUnitary.lean#L122-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/CzDiagUnitary.lean#L122-L133

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

theorem PI.WSF.cz_zariski {N : ℕ} (P : MvPolynomial (Fin N × Fin N) ℂ)
    (h : ∀ u ∈ unitaryGroup (Fin N) ℂ, evalM u P = 0) (g : Matrix (Fin N) (Fin N) ℂ)
    (hg : IsUnit g.det) : evalM g P = 0 := by sorry
