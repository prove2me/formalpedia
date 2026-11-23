-- Prove2me | Theorems.Thm_PI_DvRows_val_eq_one_of_not_mem
-- name    : PI.DvRows.val_eq_one_of_not_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:22.694939+00:00
-- url     : https://prove2.me/theorems/7e696773-5fa7-444f-bda2-a26cdaea1342
-- title:
--   Dv Rows: val eq one of not mem
-- statement:
--   The Dv Rows construction uses the val eq one of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/ValLeOneOfMemRange.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/ValLeOneOfMemRange.lean#L49-L53

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

theorem PI.DvRows.val_eq_one_of_not_mem (w : HeightOneSpectrum (𝓞 K)) (s : 𝓞 K) (hs : s ∉ w.asIdeal) :
    w.valuation K (algebraMap (𝓞 K) K s) = 1 := by sorry
