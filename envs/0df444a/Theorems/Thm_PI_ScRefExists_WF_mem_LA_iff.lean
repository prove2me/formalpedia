-- Prove2me | Theorems.Thm_PI_ScRefExists_WF_mem_LA_iff
-- name    : PI.ScRefExists.WF.mem_LA_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:18:03.593875+00:00
-- url     : https://prove2.me/theorems/747b7a3a-0ab0-4be8-9679-d2edb9386fd6
-- title:
--   WF: mem LA iff
-- statement:
--   The WF construction uses the mem LA iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/MemLAOfNsmul.lean#L28-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/MemLAOfNsmul.lean#L28-L61

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_StarMemAp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_MemLAOfNsmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk
open PI PI.ScRefExists PI.ScRefExists.WF
variable {I : Formalism.MainNotions.S.AutInst} {p : ℕ}

theorem PI.ScRefExists.WF.mem_LA_iff (hp : p.Prime) {x : Fin I.n → I.E} :
    x ∈ LA I p ↔ ∃ s : ℕ, Nat.Coprime s p ∧ (s : I.E) • x ∈ I.L := by sorry
