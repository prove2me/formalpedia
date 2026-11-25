-- Prove2me | Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_dS_conj_N_iff
-- name    : PI.NUnimodLoc.UnitaryGroupMassFormula.dS_conj_N_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:35:09.472021+00:00
-- url     : https://prove2.me/theorems/00690db2-e60a-4805-874e-7ea014f32b77
-- title:
--   Unitary Group Mass Formula: d S conj N iff
-- statement:
--   The Unitary Group Mass Formula construction uses the d S conj N iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnimodularLattice/NonstandardUnimodularLattice.lean#L20-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnimodularLattice/NonstandardUnimodularLattice.lean#L20-L36

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

theorem PI.NUnimodLoc.UnitaryGroupMassFormula.dS_conj_N_iff {k r : ℕ} {s : ℝ} (hs : s ≠ 0)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    dS k r s * g * (dS k r s)⁻¹ ∈ Nset k r ↔ g ∈ Nset k r := by sorry
