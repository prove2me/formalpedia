-- Prove2me | Theorems.Thm_PI_WSF_czFam_eval
-- name    : PI.WSF.czFam_eval
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:44:38.251605+00:00
-- url     : https://prove2.me/theorems/bfc821c7-e511-4036-826c-74994e58e9cd
-- title:
--   WSF: cz Fam eval
-- statement:
--   The WSF construction uses the cz Fam eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/CzDiagUnitary.lean#L32-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/CzDiagUnitary.lean#L32-L46

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

theorem PI.WSF.czFam_eval {N : ℕ} (u v : Matrix (Fin N) (Fin N) ℂ) (P : MvPolynomial (Fin N × Fin N) ℂ)
    (z : Fin N → ℂ) : eval z (czFam u v P) = evalM (u * diagonal z * v) P := by sorry
