-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_JCC_Ck_abs_le_of_mem_uIcc
-- name    : PI.UnitaryGroupMassFormula.JCC.Ck.abs_le_of_mem_uIcc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:11:31.534082+00:00
-- url     : https://prove2.me/theorems/18920216-427d-54f4-b5aa-0006485c1333
-- title:
--   Ck: abs le of mem u Icc
-- statement:
--   The Ck construction uses the abs le of mem u Icc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianCommutation/PCkPartials.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianCommutation/PCkPartials.lean#L55-L58

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_CkDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_PCkPartials
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Asymptotics
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.JCC PI.UnitaryGroupMassFormula.JCC.Ck
variable {d : ℕ}

theorem PI.UnitaryGroupMassFormula.JCC.Ck.abs_le_of_mem_uIcc {a s : ℝ} (hs : s ∈ Set.uIcc 0 a) : |s| ≤ |a| := by sorry
