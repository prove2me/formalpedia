-- Prove2me | Theorems.Thm_PI_ScRefExists_PPA_natCast_smul_mem_L
-- name    : PI.ScRefExists.PPA.natCast_smul_mem_L
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:23:30.655211+00:00
-- url     : https://prove2.me/theorems/665b6479-050f-4290-a8bb-94c1822f0a32
-- title:
--   PPA: nat Cast smul mem L
-- statement:
--   The PPA construction uses the nat Cast smul mem L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/NatCastSmulMemL.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/NatCastSmulMemL.lean#L67-L69

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_NatCastSmulMemL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open PI PI.ScRefExists PI.ScRefExists.PPA
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)

theorem PI.ScRefExists.PPA.natCast_smul_mem_L (s : ℕ) {x : Fin I.n → I.E} (hx : x ∈ I.L) : (s : I.E) • x ∈ I.L := by sorry
