-- Prove2me | Theorems.Thm_PI_ScRefExists_LG_Phi_tmul
-- name    : PI.ScRefExists.LG.Phi_tmul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:12:53.557843+00:00
-- url     : https://prove2.me/theorems/732a3687-2609-4c87-b419-6b5dd62cab55
-- title:
--   LG: Phi tmul
-- statement:
--   The LG construction uses the Phi tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/LocGlob.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/LocGlob.lean#L33-L35

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_LocGlob
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
open scoped TensorProduct nonZeroDivisors
open PI PI.ScRefExists PI.ScRefExists.LG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem PI.ScRefExists.LG.Phi_tmul (a x : E) (c : Af F) :
    Phi a (x ⊗ₜ[F] c) = algebraMap F (Af F) (Algebra.trace F E (a * x)) * c := by sorry
