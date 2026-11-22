-- Prove2me | Theorems.Thm_PI_WMI_lowerInv_torus_mem
-- name    : PI.WMI.lowerInv_torus_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:02:30.336052+00:00
-- url     : https://prove2.me/theorems/9944a184-b3a0-4a6c-9b90-69779ece728b
-- title:
--   WMI: lower Inv torus mem
-- statement:
--   The WMI construction uses the lower Inv torus mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/LowerInv.lean#L45-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/LowerInv.lean#L45-L54

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_LowerInv
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

theorem PI.WMI.lowerInv_torus_mem {N : ℕ} (θ : Fin N → ℝ) : torus θ ∈ Kset (allPos N) := by sorry
