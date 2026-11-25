-- Prove2me | Theorems.Thm_PI_ScRefExists_PPA_isInt_star
-- name    : PI.ScRefExists.PPA.isInt_star
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:23:51.871643+00:00
-- url     : https://prove2.me/theorems/b8f2b55f-fa89-41ea-8cd7-448cffd6d84d
-- title:
--   PPA: is Int star
-- statement:
--   The PPA construction uses the is Int star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/LocalAssemblyPrincipal.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/LocalAssemblyPrincipal.lean#L41-L42

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

theorem PI.ScRefExists.PPA.isInt_star (θ : 𝓞 I.E) : IsInt I (star (θ : I.E)) := by sorry
