-- Prove2me | Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_hJ_mulVec
-- name    : PI.ScMuExists.UnitaryGroupMassFormula.hJ_mulVec
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:37:32.800612+00:00
-- url     : https://prove2.me/theorems/f76dcee5-bd71-442e-9def-b7d366c57deb
-- title:
--   Unitary Group Mass Formula: h J mul Vec
-- statement:
--   The Unitary Group Mass Formula construction uses the h J mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ContinuousUMatApply.lean#L119-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ContinuousUMatApply.lean#L119-L124

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable {n r : ℕ}

theorem PI.ScMuExists.UnitaryGroupMassFormula.hJ_mulVec {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g)
    (x y : Fin n → ℂ) : hJ ε (g *ᵥ x) (g *ᵥ y) = hJ ε x y := by sorry
