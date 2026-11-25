-- Prove2me | Theorems.Thm_PI_WGB_rowDiv_matrixCoeffPoly_eq_zero
-- name    : PI.WGB.rowDiv_matrixCoeffPoly_eq_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:46:22.848896+00:00
-- url     : https://prove2.me/theorems/86c57978-345a-47b3-9a7b-63a371209b8f
-- title:
--   WGB: row Div matrix Coeff Poly eq zero
-- statement:
--   The WGB construction uses the row Div matrix Coeff Poly eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean#L133-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean#L133-L153

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)
variable {n k : ℕ} (f : MvPolynomial (Fin (n + k) × Fin (n + k)) ℂ)
variable {f}

theorem PI.WGB.rowDiv_matrixCoeffPoly_eq_zero (hU : ∀ u, IsUU u → rowAct ℂ (iotaC ℂ n k u).transpose f = f)
    (a b : Fin n) (hab : a < b) (kk : ℕ) (hk : 1 ≤ kk) : rowDiv ℂ a b kk (mcP f) = 0 := by sorry
