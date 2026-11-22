-- Prove2me | Theorems.Thm_PI_WeylForKWork_mem_unitaryCentralizer_allPos_iff
-- name    : PI.WeylForKWork.mem_unitaryCentralizer_allPos_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:17:51.581021+00:00
-- url     : https://prove2.me/theorems/e52becfa-e882-4aab-8d17-2e1c6be9a74e
-- title:
--   Weyl For KWork: mem unitary Centralizer all Pos iff
-- statement:
--   The Weyl For KWork construction uses the mem unitary Centralizer all Pos iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Blocks.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Blocks.lean#L60-L63

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix
variable {N : ℕ}

theorem PI.WeylForKWork.mem_unitaryCentralizer_allPos_iff (n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) : h ∈ Kset (allPos n) ↔ h ∈ unitaryGroup _ ℂ := by sorry
