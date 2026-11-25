-- Prove2me | Theorems.Thm_PI_WSF_ci_Alin_apply
-- name    : PI.WSF.ci_Alin_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:48:29.643294+00:00
-- url     : https://prove2.me/theorems/07711d6d-002a-57aa-98b4-60b25dfd92dc
-- title:
--   WSF: ci Alin apply
-- statement:
--   The WSF construction uses the ci Alin apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/CiEvalMSmul.lean#L85-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/CiEvalMSmul.lean#L85-L86

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CrRowActRowAct
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CiEvalMSmul
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
open MvPolynomial MeasureTheory Matrix

theorem PI.WSF.ci_Alin_apply {N : ℕ} {μ : Measure (Matrix (Fin N) (Fin N) ℂ)} (hμ : IsHaarU N μ)
    (p q : MvPolynomial (Fin N × Fin N) ℂ) : Alin hμ q p = Aform μ p q := by sorry
