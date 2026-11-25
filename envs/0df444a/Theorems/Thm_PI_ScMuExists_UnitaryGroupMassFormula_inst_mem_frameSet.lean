-- Prove2me | Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_inst_mem_frameSet
-- name    : PI.ScMuExists.UnitaryGroupMassFormula.inst_mem_frameSet
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:05:39.410668+00:00
-- url     : https://prove2.me/theorems/fc59df48-425a-5c83-9575-6b51472077bc
-- title:
--   Unitary Group Mass Formula: inst mem frame Set
-- statement:
--   The Unitary Group Mass Formula construction uses the inst mem frame Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/InstTop.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/InstTop.lean#L11-L13

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory NumberField Matrix
open scoped ENNReal Pointwise
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula

theorem PI.ScMuExists.UnitaryGroupMassFormula.inst_mem_frameSet {I : Formalism.MainNotions.S.AutInst} {r : ℕ} (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (j : Fin r ⊕ Fin r ⊕ Unit) : instFvec e f z j ∈ frameSet I e f z := by sorry
