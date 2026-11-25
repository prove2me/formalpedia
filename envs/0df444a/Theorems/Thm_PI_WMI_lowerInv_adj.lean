-- Prove2me | Theorems.Thm_PI_WMI_lowerInv_adj
-- name    : PI.WMI.lowerInv_adj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:58:59.227583+00:00
-- url     : https://prove2.me/theorems/9156aa2c-6ef2-478c-97f6-c7759664d24b
-- title:
--   WMI: lower Inv adj
-- statement:
--   The WMI construction uses the lower Inv adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/LowerInv.lean#L106-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/LowerInv.lean#L106-L113

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
variable {N : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)}

theorem PI.WMI.lowerInv_adj (hU : IsURepOn (Kset (allPos N)) σ) (θ : Fin N → ℝ) (y w : H) :
    ⟪y, σ (torus θ) w⟫_ℂ = ⟪σ (torus (-θ)) y, w⟫_ℂ := by sorry
