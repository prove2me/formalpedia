-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_local_contract
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.local_contract
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:08:16.686831+00:00
-- url     : https://prove2.me/theorems/1024caaf-4f5b-51b4-b725-947dbf399383
-- title:
--   Unitary Group Mass Formula: local contract
-- statement:
--   The Unitary Group Mass Formula construction uses the local contract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/MeasureContractionFormula.lean#L51-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/MeasureContractionFormula.lean#L51-L80

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

theorem PI.NMeasInv.UnitaryGroupMassFormula.local_contract (hG : Gram ε e f) {z : Fin n → ℂ} (g : Formalism.REAL.UJ ε)
    (hgN : InN ε e z (Formalism.MainNotions.S.uMat g)) (hg'N : InN ε e z (Formalism.MainNotions.S.uMat g⁻¹)) :
    ∃ s : Fin r → ℝ, ∃ hs : ∀ b, s b ≠ 0, Formalism.MainNotions.S.uMat (aUJ hG s hs * g * (aUJ hG s hs)⁻¹) ∈ Cmat n := by sorry
