-- Prove2me | Theorems.Thm_PI_ScRefExists_WF_dual_LA
-- name    : PI.ScRefExists.WF.dual_LA
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:37:46.51991+00:00
-- url     : https://prove2.me/theorems/d692612c-2cd4-4423-a135-4bd5ff28a9e0
-- title:
--   WF: dual LA
-- statement:
--   The WF construction uses the dual LA property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/MemLAOfNsmul.lean#L74-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/MemLAOfNsmul.lean#L74-L102

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

theorem PI.ScRefExists.WF.dual_LA (hp : p.Prime) {x : Fin I.n → I.E} (hx : ∀ y ∈ I.L, hG I y x ∈ Ap I p) : x ∈ LA I p := by sorry
