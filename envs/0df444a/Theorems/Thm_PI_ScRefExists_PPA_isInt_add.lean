-- Prove2me | Theorems.Thm_PI_ScRefExists_PPA_isInt_add
-- name    : PI.ScRefExists.PPA.isInt_add
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:27:06.021881+00:00
-- url     : https://prove2.me/theorems/f577555c-2bb7-5b5b-b4a5-513d1e3ff50a
-- title:
--   PPA: is Int add
-- statement:
--   The PPA construction uses the is Int add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/LocalAssemblyPrincipal.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/LocalAssemblyPrincipal.lean#L30-L33

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

theorem PI.ScRefExists.PPA.isInt_add {x y : I.E} (hx : IsInt I x) (hy : IsInt I y) : IsInt I (x + y) := by sorry
