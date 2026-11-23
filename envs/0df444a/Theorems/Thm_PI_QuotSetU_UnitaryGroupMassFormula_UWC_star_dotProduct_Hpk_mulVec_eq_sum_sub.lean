-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_UWC_star_dotProduct_Hpk_mulVec_eq_sum_sub
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.UWC.star_dotProduct_Hpk_mulVec_eq_sum_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:39:39.817552+00:00
-- url     : https://prove2.me/theorems/8cf4cbfd-e032-4a54-a65e-6fbfeaae827d
-- title:
--   UWC: star dot Product Hpk mul Vec eq sum sub
-- statement:
--   The UWC construction uses the star dot Product Hpk mul Vec eq sum sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/UnitaryWeylCompact.lean#L19-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/UnitaryWeylCompact.lean#L19-L48

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnitaryWeylCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.UWC
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula.SW
variable {k r : ℕ}

theorem PI.QuotSetU.UnitaryGroupMassFormula.UWC.star_dotProduct_Hpk_mulVec_eq_sum_sub (v w : Fin (2 * r + k + 1) → ℂ) (hv : ∀ i, ¬ inW k r i → v i = 0) :
    star w ⬝ᵥ (Hpk k r *ᵥ v) =
      (∑ i ∈ Wp k r, star (w i) * v i) - star (w (lI k r)) * v (lI k r) := by sorry
