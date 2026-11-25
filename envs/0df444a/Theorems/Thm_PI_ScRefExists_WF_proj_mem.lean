-- Prove2me | Theorems.Thm_PI_ScRefExists_WF_proj_mem
-- name    : PI.ScRefExists.WF.proj_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:16:45.6469+00:00
-- url     : https://prove2.me/theorems/96459332-9961-4902-8d11-bf7ae094a9c0
-- title:
--   WF: proj mem
-- statement:
--   The WF construction uses the proj mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/MemLAOfNsmul.lean#L171-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/MemLAOfNsmul.lean#L171-L179

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

theorem PI.ScRefExists.WF.proj_mem (hp : p.Prime) {r : ℕ} {e f : Fin r → Fin I.n → I.E}
    (heA : ∀ a, e a ∈ LA I p) (hfA : ∀ a, f a ∈ LA I p) {y : Fin I.n → I.E} (hy : y ∈ LA I p) :
    proj e f y ∈ LA I p := by sorry
