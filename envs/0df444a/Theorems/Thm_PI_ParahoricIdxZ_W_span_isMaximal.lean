-- Prove2me | Theorems.Thm_PI_ParahoricIdxZ_W_span_isMaximal
-- name    : PI.ParahoricIdxZ.W.span_isMaximal
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:36:07.420089+00:00
-- url     : https://prove2.me/theorems/49f84d4b-bbfe-436d-98a1-224d9829d207
-- title:
--   W: span is Maximal
-- statement:
--   The W construction uses the span is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/SpanIsMaximal.lean#L10-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/SpanIsMaximal.lean#L10-L30

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_SpanIsMaximal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W

theorem PI.ParahoricIdxZ.W.span_isMaximal {F : Type} [Field F] (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O)
    (hloc : Formalism.DoubleCosetMeasures.IsLocalAt O ϖ) : (Ideal.span {(⟨ϖ, hϖ⟩ : O)}).IsMaximal := by sorry
