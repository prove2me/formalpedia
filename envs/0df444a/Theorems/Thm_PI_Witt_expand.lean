-- Prove2me | Theorems.Thm_PI_Witt_expand
-- name    : PI.Witt.expand
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:07:05.973355+00:00
-- url     : https://prove2.me/theorems/1037fd0f-e488-48f6-a564-fb2d6124b057
-- title:
--   Witt: expand
-- statement:
--   The Witt construction uses the expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittDecomposition/EnlargeStep.lean#L8-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittDecomposition/EnlargeStep.lean#L8-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_EnlargeStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Witt
variable {K V : Type} [Field K] [StarRing K] [CharZero K] [AddCommGroup V] [Module K V]

theorem PI.Witt.expand (B : V →ₗ⋆[K] V →ₗ[K] K) (p u u' : V) (c c' : K) :
    B (u + c • p) (u' + c' • p) =
      B u u' + c' * B u p + star c * B p u' + star c * c' * B p p := by sorry
