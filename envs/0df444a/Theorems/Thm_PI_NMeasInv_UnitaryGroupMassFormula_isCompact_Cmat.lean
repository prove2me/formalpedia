-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_isCompact_Cmat
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.isCompact_Cmat
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:03:38.001635+00:00
-- url     : https://prove2.me/theorems/9644cbcf-80b5-49fd-8aea-052370195a56
-- title:
--   Unitary Group Mass Formula: is Compact Cmat
-- statement:
--   The Unitary Group Mass Formula construction uses the is Compact Cmat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/MeasureContractionFormula.lean#L36-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/MeasureContractionFormula.lean#L36-L46

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

theorem PI.NMeasInv.UnitaryGroupMassFormula.isCompact_Cmat (n : ℕ) : IsCompact (Cmat n) := by sorry
