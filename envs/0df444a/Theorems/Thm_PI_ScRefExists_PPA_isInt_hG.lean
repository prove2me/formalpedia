-- Prove2me | Theorems.Thm_PI_ScRefExists_PPA_isInt_hG
-- name    : PI.ScRefExists.PPA.isInt_hG
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:24:09.901811+00:00
-- url     : https://prove2.me/theorems/87128702-ac07-4378-b65d-d1821a83fc57
-- title:
--   PPA: is Int h G
-- statement:
--   The PPA construction uses the is Int h G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/LocalAssemblyPrincipal.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/LocalAssemblyPrincipal.lean#L37-L39

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

theorem PI.ScRefExists.PPA.isInt_hG {x y : Fin I.n → I.E} (hx : x ∈ I.L) (hy : y ∈ I.L) : IsInt I (hG I x y) := by sorry
