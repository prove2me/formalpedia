-- Prove2me | Theorems.Thm_PI_ScRefExists_WF_inv_mem_Ap
-- name    : PI.ScRefExists.WF.inv_mem_Ap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:00:34.182698+00:00
-- url     : https://prove2.me/theorems/667ce149-a521-41f7-b83f-b556c311c824
-- title:
--   WF: inv mem Ap
-- statement:
--   The WF construction uses the inv mem Ap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/StarMemAp.lean#L113-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/StarMemAp.lean#L113-L119

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_StarMemAp
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
open Matrix
open PI PI.ScRefExists PI.ScRefExists.WF
variable (I : Formalism.MainNotions.S.AutInst)
variable {I}

theorem PI.ScRefExists.WF.inv_mem_Ap {p s : ℕ} (hp : p.Prime) (hs : Nat.Coprime s p) : ((s : I.E))⁻¹ ∈ Ap I p := by sorry
