-- Prove2me | Theorems.Thm_PI_ScRefExists_WF_hG_LA
-- name    : PI.ScRefExists.WF.hG_LA
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:20:09.217578+00:00
-- url     : https://prove2.me/theorems/a6bfcb87-fd6d-4745-b59b-0dc4fc604f34
-- title:
--   WF: h G LA
-- statement:
--   The WF construction uses the h G LA property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/MemLAOfNsmul.lean#L65-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/MemLAOfNsmul.lean#L65-L72

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

theorem PI.ScRefExists.WF.hG_LA (hp : p.Prime) {x y : Fin I.n → I.E} (hx : x ∈ LA I p) (hy : y ∈ LA I p) :
    hG I x y ∈ Ap I p := by sorry
