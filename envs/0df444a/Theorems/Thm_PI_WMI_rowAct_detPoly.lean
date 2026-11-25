-- Prove2me | Theorems.Thm_PI_WMI_rowAct_detPoly
-- name    : PI.WMI.rowAct_detPoly
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:47:47.145799+00:00
-- url     : https://prove2.me/theorems/28f65d92-de45-4edb-8064-54e292613fce
-- title:
--   WMI: row Act det Poly
-- statement:
--   The WMI construction uses the row Act det Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/Assembly.lean#L29-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/Assembly.lean#L29-L37

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_Assembly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

theorem PI.WMI.rowAct_detPoly {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    rowAct ℂ (n := N) A (detPoly N) = C A.det * detPoly N := by sorry
