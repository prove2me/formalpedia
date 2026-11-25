-- Prove2me | Theorems.Thm_PI_DvRows_val_le_one_of_mem_range
-- name    : PI.DvRows.val_le_one_of_mem_range
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:45.596337+00:00
-- url     : https://prove2.me/theorems/d1e036e6-6a67-461f-b5d4-336ec94cbfb8
-- title:
--   Dv Rows: val le one of mem range
-- statement:
--   The Dv Rows construction uses the val le one of mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/ValLeOneOfMemRange.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/ValLeOneOfMemRange.lean#L55-L58

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_ValLeOneOfMemRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem PI.DvRows.val_le_one_of_mem_range (w : HeightOneSpectrum (𝓞 K)) (x : K)
    (hx : x ∈ Set.range (algebraMap (𝓞 K) K)) : w.valuation K x ≤ 1 := by sorry
