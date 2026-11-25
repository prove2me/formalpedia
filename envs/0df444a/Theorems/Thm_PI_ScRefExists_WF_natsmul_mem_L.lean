-- Prove2me | Theorems.Thm_PI_ScRefExists_WF_natsmul_mem_L
-- name    : PI.ScRefExists.WF.natsmul_mem_L
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:43:19.439645+00:00
-- url     : https://prove2.me/theorems/f0c196ed-767b-5fe5-b6bd-967205512ce0
-- title:
--   WF: natsmul mem L
-- statement:
--   The WF construction uses the natsmul mem L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/MemLAOfNsmul.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/MemLAOfNsmul.lean#L23-L26

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

theorem PI.ScRefExists.WF.natsmul_mem_L {s : ℕ} {x : Fin I.n → I.E} (hx : x ∈ I.L) : (s : I.E) • x ∈ I.L := by sorry
