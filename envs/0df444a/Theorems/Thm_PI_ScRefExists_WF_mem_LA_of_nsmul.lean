-- Prove2me | Theorems.Thm_PI_ScRefExists_WF_mem_LA_of_nsmul
-- name    : PI.ScRefExists.WF.mem_LA_of_nsmul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:38:08.156649+00:00
-- url     : https://prove2.me/theorems/eac088a2-719f-45e1-8163-1ebd3ecfc578
-- title:
--   WF: mem LA of nsmul
-- statement:
--   The WF construction uses the mem LA of nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/MemLAOfNsmul.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/MemLAOfNsmul.lean#L104-L107

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

theorem PI.ScRefExists.WF.mem_LA_of_nsmul (hp : p.Prime) {M : ℕ} (hM : Nat.Coprime M p) {x : Fin I.n → I.E}
    (hx : M • x ∈ I.L) : x ∈ LA I p := by sorry
