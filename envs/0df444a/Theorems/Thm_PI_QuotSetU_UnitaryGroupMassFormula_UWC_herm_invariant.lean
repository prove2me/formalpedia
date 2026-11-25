-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_UWC_herm_invariant
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.UWC.herm_invariant
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:19:11.544069+00:00
-- url     : https://prove2.me/theorems/98e6a162-d5f4-557d-ad80-6e1583430624
-- title:
--   UWC: herm invariant
-- statement:
--   The UWC construction uses the herm invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/UnitaryWeylCompact.lean#L64-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/UnitaryWeylCompact.lean#L64-L69

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

theorem PI.QuotSetU.UnitaryGroupMassFormula.UWC.herm_invariant {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UH (Hpk k r)) (u v : Fin (2 * r + k + 1) → ℂ) :
    star (h *ᵥ u) ⬝ᵥ (Hpk k r *ᵥ (h *ᵥ v)) = star u ⬝ᵥ (Hpk k r *ᵥ v) := by sorry
