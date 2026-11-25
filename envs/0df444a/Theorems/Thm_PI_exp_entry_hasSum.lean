-- Prove2me | Theorems.Thm_PI_exp_entry_hasSum
-- name    : PI.exp_entry_hasSum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:54:01.902536+00:00
-- url     : https://prove2.me/theorems/132f5f28-1d64-5bed-8cd8-b3af94cfabb7
-- title:
--   PI: exp entry has Sum
-- statement:
--   The PI construction uses the exp entry has Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ContinuousExpLie.lean#L131-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ContinuousExpLie.lean#L131-L136

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
open scoped Matrix.Norms.Operator

theorem PI.exp_entry_hasSum (X : Mx k r) (i j : Fin (2 * r + k + 1)) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) * (X ^ n) i j) ((NormedSpace.exp X) i j) := by sorry
