-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_IndexUBound_one_sub_sum_le_prod
-- name    : PI.UnitaryGroupMassFormula.IndexUBound.one_sub_sum_le_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:27.986904+00:00
-- url     : https://prove2.me/theorems/1b493dae-6b92-4d54-83b2-ee5ff5e33b9f
-- title:
--   Index UBound: one sub sum le prod
-- statement:
--   The Index UBound construction uses the one sub sum le prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexUpperBound/OneSubSumLeProd.lean#L8-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexUpperBound/OneSubSumLeProd.lean#L8-L23

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IndexUBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexUpperBound_OneSubSumLeProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.IndexUBound
open Finset

theorem PI.UnitaryGroupMassFormula.IndexUBound.one_sub_sum_le_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (P b : ι → ℝ)
    (hP0 : ∀ i ∈ s, 0 ≤ P i) (hP1 : ∀ i ∈ s, P i ≤ 1) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hPb : ∀ i ∈ s, 1 - b i ≤ P i) : 1 - ∑ i ∈ s, b i ≤ ∏ i ∈ s, P i := by sorry
