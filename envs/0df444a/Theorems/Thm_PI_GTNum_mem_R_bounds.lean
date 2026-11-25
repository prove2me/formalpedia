-- Prove2me | Theorems.Thm_PI_GTNum_mem_R_bounds
-- name    : PI.GTNum.mem_R_bounds
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:31:09.50626+00:00
-- url     : https://prove2.me/theorems/c939d475-6aee-4599-bc63-73217b9671f4
-- title:
--   GTNum: mem R bounds
-- statement:
--   The GTNum construction uses the mem R bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/InterlacingDefectEqCard.lean#L84-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/InterlacingDefectEqCard.lean#L84-L95

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_CardEraseIccMin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_InterlacingDefectEqCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GTNum
open Formalism.BasicNotions PI Finset
variable {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)

theorem PI.GTNum.mem_R_bounds (hI : Interlace h lam sg) (hn : 0 < n) (i : Fin n) (v : ℤ)
    (hv : v ∈ Rset h lam sg i) :
    lam.w ⟨N - 1, by omega⟩ ≤ v ∧
      v ≤ sg.w ⟨0, hn⟩ + (sg.w ⟨0, hn⟩ - lam.w ⟨N - 1, by omega⟩) := by sorry
