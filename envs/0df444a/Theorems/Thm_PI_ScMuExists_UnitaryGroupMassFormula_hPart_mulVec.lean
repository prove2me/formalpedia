-- Prove2me | Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_hPart_mulVec
-- name    : PI.ScMuExists.UnitaryGroupMassFormula.hPart_mulVec
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:41:20.854569+00:00
-- url     : https://prove2.me/theorems/69dc9a32-498f-5cbf-a41c-4d106b1e932f
-- title:
--   Unitary Group Mass Formula: h Part mul Vec
-- statement:
--   The Unitary Group Mass Formula construction uses the h Part mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ContinuousHPart.lean#L142-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ContinuousHPart.lean#L142-L146

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HJMulVecGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousHPart
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
variable {n r : ℕ} (ε : Fin n → Bool)
variable {ε}
variable {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ}

theorem PI.ScMuExists.UnitaryGroupMassFormula.hPart_mulVec (g : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    hPart ε e f z g *ᵥ x = x - piW ε e f z x + piW ε e f z (g *ᵥ piW ε e f z x) := by sorry
