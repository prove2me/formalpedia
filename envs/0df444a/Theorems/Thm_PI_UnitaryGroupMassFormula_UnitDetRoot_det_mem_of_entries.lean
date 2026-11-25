-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_det_mem_of_entries
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.det_mem_of_entries
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:33:54.563196+00:00
-- url     : https://prove2.me/theorems/f9cdc547-780a-5e87-9779-5801a8dac915
-- title:
--   Unit Det Root: det mem of entries
-- statement:
--   The Unit Det Root construction uses the det mem of entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/DetMemOfEntries.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/DetMemOfEntries.lean#L10-L13

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NsmulRelIdxMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_DetMemOfEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.det_mem_of_entries {m : Type} [Fintype m] [DecidableEq m] {S : IntermediateField ℚ ℂ}
    (U : Matrix m m ℂ) (h : ∀ i j, U i j ∈ S) : U.det ∈ S := by sorry
