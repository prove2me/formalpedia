-- Prove2me | Theorems.Thm_PI_ScRefExists_PPA_isInt_mul
-- name    : PI.ScRefExists.PPA.isInt_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:25:43.505211+00:00
-- url     : https://prove2.me/theorems/4fffb501-54e9-5608-aeb1-e0b1f9a36281
-- title:
--   PPA: is Int mul
-- statement:
--   The PPA construction uses the is Int mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/LocalAssemblyPrincipal.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/LocalAssemblyPrincipal.lean#L20-L23

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

theorem PI.ScRefExists.PPA.isInt_mul {x y : I.E} (hx : IsInt I x) (hy : IsInt I y) : IsInt I (x * y) := by sorry
