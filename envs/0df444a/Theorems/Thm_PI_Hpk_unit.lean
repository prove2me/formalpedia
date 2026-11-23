-- Prove2me | Theorems.Thm_PI_Hpk_unit
-- name    : PI.Hpk_unit
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:18.04278+00:00
-- url     : https://prove2.me/theorems/5412d155-7d8b-4184-bb57-e85a2c12e2ca
-- title:
--   PI: Hpk unit
-- statement:
--   The PI construction uses the Hpk unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ContinuousExpLie.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ContinuousExpLie.lean#L56-L59

import Definitions.Def_Formalism_PeriodIntegrals_HaarDefs
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_ContinuousExpLie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff
noncomputable section
open PI
open Formalism.QuantumDeterminants
variable {k r : ℕ}

theorem PI.Hpk_unit (k r : ℕ) : IsUnit (Hpk k r).det := by sorry
