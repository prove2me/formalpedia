-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_wt_ge
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.wt_ge
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:04:29.392565+00:00
-- url     : https://prove2.me/theorems/421c644f-8bf7-4350-a3fb-9ccb0a161d06
-- title:
--   Unitary Group Mass Formula: wt ge
-- statement:
--   The Unitary Group Mass Formula construction uses the wt ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/MeasureContractionFormula.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/MeasureContractionFormula.lean#L20-L24

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_ConjSubMulVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HJMulVecGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_MeasureContractionFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory NumberField
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
variable {n r : ℕ} {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ}

theorem PI.NMeasInv.UnitaryGroupMassFormula.wt_ge (lam : ℝ) (hlam : 1 ≤ lam) (b : Fin r) : lam ≤ wt r lam b := by sorry
