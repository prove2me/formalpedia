-- Prove2me | Theorems.Thm_PI_WMI_det_ne_zero_of_mem_K
-- name    : PI.WMI.det_ne_zero_of_mem_K
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:47:27.9038+00:00
-- url     : https://prove2.me/theorems/d429bae6-6531-4782-8920-6bd49422a8b9
-- title:
--   WMI: det ne zero of mem K
-- statement:
--   The WMI construction uses the det ne zero of mem K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/Assembly.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/Assembly.lean#L10-L17

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

theorem PI.WMI.det_ne_zero_of_mem_K {N : ℕ} {g : Matrix (Fin N) (Fin N) ℂ} (hg : g ∈ Kset (allPos N)) :
    g.det ≠ 0 := by sorry
