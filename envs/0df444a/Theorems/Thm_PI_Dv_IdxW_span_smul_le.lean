-- Prove2me | Theorems.Thm_PI_Dv_IdxW_span_smul_le
-- name    : PI.Dv.IdxW.span_smul_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:34.483803+00:00
-- url     : https://prove2.me/theorems/0cfb03e8-d0b3-5c3e-867f-80bcfe450357
-- title:
--   Idx W: span smul le
-- statement:
--   The Idx W construction uses the span smul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/SmulMemSpanSmul.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/SmulMemSpanSmul.lean#L26-L32

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

theorem PI.Dv.IdxW.span_smul_le (c : R) (M N : Submodule R V) (h : ∀ x ∈ M, c • x ∈ N) :
    Ideal.span {c} • M ≤ N := by sorry
