-- Prove2me | Theorems.Thm_PI_WMI_detPoly_ne_zero
-- name    : PI.WMI.detPoly_ne_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:47:29.603387+00:00
-- url     : https://prove2.me/theorems/6da58167-2066-4901-b4e8-e2118e5a9500
-- title:
--   WMI: det Poly ne zero
-- statement:
--   The WMI construction uses the det Poly ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/Assembly.lean#L19-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/Assembly.lean#L19-L27

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

theorem PI.WMI.detPoly_ne_zero (N : ℕ) : detPoly N ≠ 0 := by sorry
