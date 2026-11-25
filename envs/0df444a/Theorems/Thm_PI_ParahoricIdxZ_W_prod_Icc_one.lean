-- Prove2me | Theorems.Thm_PI_ParahoricIdxZ_W_prod_Icc_one
-- name    : PI.ParahoricIdxZ.W.prod_Icc_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:35:57.56459+00:00
-- url     : https://prove2.me/theorems/b3c89a37-bb22-471f-af80-2dbaae6d3862
-- title:
--   W: prod Icc one
-- statement:
--   The W construction uses the prod Icc one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/SpanIsMaximal.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/SpanIsMaximal.lean#L32-L36

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

theorem PI.ParahoricIdxZ.W.prod_Icc_one (g : ℕ → ℝ) (n : ℕ) : ∏ i ∈ Icc 1 n, g i = ∏ j ∈ range n, g (j + 1) := by sorry
