-- Prove2me | Theorems.Thm_PI_Dv_IdxW_smul_mem_span_smul
-- name    : PI.Dv.IdxW.smul_mem_span_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:52.235906+00:00
-- url     : https://prove2.me/theorems/715fc143-bdb7-4427-b9d0-fc819fb40bb7
-- title:
--   Idx W: smul mem span smul
-- statement:
--   The Idx W construction uses the smul mem span smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/SmulMemSpanSmul.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/SmulMemSpanSmul.lean#L34-L36

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

theorem PI.Dv.IdxW.smul_mem_span_smul (c : R) (M : Submodule R V) {x : V} (hx : x ∈ M) :
    c • x ∈ Ideal.span {c} • M := by sorry
