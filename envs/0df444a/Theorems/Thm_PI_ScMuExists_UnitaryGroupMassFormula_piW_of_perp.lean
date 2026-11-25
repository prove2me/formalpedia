-- Prove2me | Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_piW_of_perp
-- name    : PI.ScMuExists.UnitaryGroupMassFormula.piW_of_perp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:00:01.451408+00:00
-- url     : https://prove2.me/theorems/13ddc999-3361-45c0-abdd-2dbc4acc3335
-- title:
--   Unitary Group Mass Formula: pi W of perp
-- statement:
--   The Unitary Group Mass Formula construction uses the pi W of perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ContinuousHPart.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ContinuousHPart.lean#L97-L100

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

theorem PI.ScMuExists.UnitaryGroupMassFormula.piW_of_perp {y : Fin n → ℂ} (he : ∀ a, hJ ε (e a) y = 0) (hf : ∀ a, hJ ε (f a) y = 0)
    (hz : hJ ε z y = 0) : piW ε e f z y = y := by sorry
