-- Prove2me | Theorems.Thm_PI_WMI_lowerInv_inner_pres
-- name    : PI.WMI.lowerInv_inner_pres
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:47:00.267585+00:00
-- url     : https://prove2.me/theorems/db13349a-42b9-43ac-aab5-1068a5db6c7f
-- title:
--   WMI: lower Inv inner pres
-- statement:
--   The WMI construction uses the lower Inv inner pres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/LowerInv.lean#L101-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/LowerInv.lean#L101-L104

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

theorem PI.WMI.lowerInv_inner_pres (hU : IsURepOn (Kset (allPos N)) σ) {g : Matrix (Fin N) (Fin N) ℂ}
    (hg : g ∈ Kset (allPos N)) (u w : H) : ⟪σ g u, σ g w⟫_ℂ = ⟪u, w⟫_ℂ := by sorry
