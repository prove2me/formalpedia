-- Prove2me | Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_exists_conj_box
-- name    : PI.NUnimodLoc.UnitaryGroupMassFormula.exists_conj_box
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:35:20.380848+00:00
-- url     : https://prove2.me/theorems/0c5f8538-7f21-4ba0-b910-be2a3b28c534
-- title:
--   Unitary Group Mass Formula: exists conj box
-- statement:
--   The Unitary Group Mass Formula construction uses the exists conj box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnimodularLattice/NonstandardUnimodularLattice.lean#L38-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnimodularLattice/NonstandardUnimodularLattice.lean#L38-L54

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ExistsModularFunction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsCompactInterUnitBox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_NonstandardUnimodularLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open PI PI.NUnimodLoc PI.NUnimodLoc.UnitaryGroupMassFormula
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW

theorem PI.NUnimodLoc.UnitaryGroupMassFormula.exists_conj_box {k r : ℕ} {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hn : n ∈ Nset k r) :
    ∃ s : ℝ, 0 < s ∧ ∀ i j, ‖(dS k r s * n * (dS k r s)⁻¹ - 1) i j‖ ≤ 1 := by sorry
