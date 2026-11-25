-- Prove2me | Theorems.Thm_PI_WMI_lowerInv_evM_affine
-- name    : PI.WMI.lowerInv_evM_affine
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:47:35.530603+00:00
-- url     : https://prove2.me/theorems/6122ac3b-c1e6-416c-82fe-365e75e31def
-- title:
--   WMI: lower Inv ev M affine
-- statement:
--   The WMI construction uses the lower Inv ev M affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/LowerInv.lean#L24-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/LowerInv.lean#L24-L43

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

theorem PI.WMI.lowerInv_evM_affine {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ)
    (Q : MvPolynomial (Fin N × Fin N) ℂ) :
    ∃ p : Polynomial ℂ, ∀ c : ℂ, evM (A + c • B) Q = p.eval c := by sorry
