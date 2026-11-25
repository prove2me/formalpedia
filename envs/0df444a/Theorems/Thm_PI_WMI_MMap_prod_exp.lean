-- Prove2me | Theorems.Thm_PI_WMI_MMap_prod_exp
-- name    : PI.WMI.MMap.prod_exp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:01:35.848095+00:00
-- url     : https://prove2.me/theorems/d4eb6d26-7384-5bc5-9920-e2513a07ddd2
-- title:
--   MMap: prod exp
-- statement:
--   The MMap construction uses the prod exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean#L89-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean#L89-L97

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_ModelMap
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
open PI.WMI.MMap

theorem PI.WMI.MMap.prod_exp {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (θ : Fin N → ℝ) :
    ∏ v : Fin N × Fin N, Complex.exp ((θ v.2 : ℂ) * Complex.I) ^ m v =
      Complex.exp (((∑ v : Fin N × Fin N, (m v : ℝ) * θ v.2 : ℝ) : ℂ) * Complex.I) := by sorry
