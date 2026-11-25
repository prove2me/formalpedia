-- Prove2me | Theorems.Thm_PI_Dv_IdxW_comap_smul_top
-- name    : PI.Dv.IdxW.comap_smul_top
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:44.214954+00:00
-- url     : https://prove2.me/theorems/e70b44f8-ae5f-5cd3-856f-229b6b142318
-- title:
--   Idx W: comap smul top
-- statement:
--   The Idx W construction uses the comap smul top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/SmulMemSpanSmul.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/SmulMemSpanSmul.lean#L15-L19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_IsLocalizedModuleToSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_SmulMemSpanSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.IdxW
open NumberField IsDedekindDomain Module
variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

theorem PI.Dv.IdxW.comap_smul_top (I : Ideal R) (M : Submodule R V) :
    (I • M).comap M.subtype = I • (⊤ : Submodule R M) := by sorry
