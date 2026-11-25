-- Prove2me | Theorems.Thm_PI_continuous_of
-- name    : PI.continuous_of
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:24:40.865549+00:00
-- url     : https://prove2.me/theorems/16259e03-887c-4cae-8bdb-126bfa9a86ce
-- title:
--   PI: continuous of
-- statement:
--   The PI construction uses the continuous of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ContinuousExpLie.lean#L200-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ContinuousExpLie.lean#L200-L200

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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem PI.continuous_of : Continuous (fun x : Mt k r => (Matrix.of x : Mx k r)) := by sorry
