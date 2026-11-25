-- Prove2me | Theorems.Thm_PI_WSF_ci_invariant
-- name    : PI.WSF.ci_invariant
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:46:40.840459+00:00
-- url     : https://prove2.me/theorems/1593b236-9e5a-449d-85d5-09f9ce9046a8
-- title:
--   WSF: ci invariant
-- statement:
--   The WSF construction uses the ci invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/CiEvalMSmul.lean#L112-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/CiEvalMSmul.lean#L112-L118

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

theorem PI.WSF.ci_invariant {N : ℕ} {μ : Measure (Matrix (Fin N) (Fin N) ℂ)} (hμ : IsHaarU N μ)
    (u : Matrix (Fin N) (Fin N) ℂ) (hu : u ∈ unitaryGroup (Fin N) ℂ) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    Aform μ (Formalism.GradedWeylDivisibility.rowAct ℂ u p) (Formalism.GradedWeylDivisibility.rowAct ℂ u q) = Aform μ p q := by sorry
