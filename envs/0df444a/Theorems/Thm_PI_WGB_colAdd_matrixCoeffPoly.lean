-- Prove2me | Theorems.Thm_PI_WGB_colAdd_matrixCoeffPoly
-- name    : PI.WGB.colAdd_matrixCoeffPoly
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:45:20.829168+00:00
-- url     : https://prove2.me/theorems/419c985c-7702-52a8-9f20-acb5cc95f4ce
-- title:
--   WGB: col Add matrix Coeff Poly
-- statement:
--   The WGB construction uses the col Add matrix Coeff Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean#L118-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean#L118-L131

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

theorem PI.WGB.colAdd_matrixCoeffPoly (hU : ∀ u, IsUU u → rowAct ℂ (iotaC ℂ n k u).transpose f = f)
    (l j : Fin n) (hlj : l < j) (c : ℂ) : colAdd ℂ l j c (mcP f) = mcP f := by sorry
