-- Prove2me | Theorems.Thm_PI_WGB_eval_matrixCoeffPoly
-- name    : PI.WGB.eval_matrixCoeffPoly
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:00:41.158483+00:00
-- url     : https://prove2.me/theorems/4f3f7be2-54a8-4a70-8b50-45d2f2eac600
-- title:
--   WGB: eval matrix Coeff Poly
-- statement:
--   The WGB construction uses the eval matrix Coeff Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean#L55-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean#L55-L66

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

theorem PI.WGB.eval_matrixCoeffPoly (x : Fin n × Fin n → ℂ) : eval x (mcP f) = mcF f (matOf x) := by sorry
