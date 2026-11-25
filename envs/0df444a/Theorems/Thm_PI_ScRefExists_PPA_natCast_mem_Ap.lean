-- Prove2me | Theorems.Thm_PI_ScRefExists_PPA_natCast_mem_Ap
-- name    : PI.ScRefExists.PPA.natCast_mem_Ap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:23:54.113595+00:00
-- url     : https://prove2.me/theorems/66344a1d-b7b4-4332-9bc3-03e8b7d7c800
-- title:
--   PPA: nat Cast mem Ap
-- statement:
--   The PPA construction uses the nat Cast mem Ap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/LocalAssemblyPrincipal.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/LocalAssemblyPrincipal.lean#L44-L46

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_SpanSmulInto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_LocalAssemblyPrincipal
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

theorem PI.ScRefExists.PPA.natCast_mem_Ap (p s : ℕ) : (s : I.E) ∈ Ap I p := by sorry
