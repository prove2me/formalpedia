-- Prove2me | Theorems.Thm_PI_WGB_isUU_E
-- name    : PI.WGB.isUU_E
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:47:44.874805+00:00
-- url     : https://prove2.me/theorems/2fca522b-1589-48e1-a138-729061343459
-- title:
--   WGB: is UU E
-- statement:
--   The WGB construction uses the is UU E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean#L95-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean#L95-L104

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

theorem PI.WGB.isUU_E (l j : Fin n) (hlj : l < j) (c : ℂ) : IsUU (Formalism.UG.P.wlocal_E l j c) := by sorry
