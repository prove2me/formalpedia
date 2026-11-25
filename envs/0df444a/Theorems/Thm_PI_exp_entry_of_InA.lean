-- Prove2me | Theorems.Thm_PI_exp_entry_of_InA
-- name    : PI.exp_entry_of_InA
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:25.535947+00:00
-- url     : https://prove2.me/theorems/95524014-2bc3-58bc-b3d1-350b6b9359b1
-- title:
--   PI: exp entry of In A
-- statement:
--   The PI construction uses the exp entry of In A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ContinuousExpLie.lean#L138-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ContinuousExpLie.lean#L138-L147

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

theorem PI.exp_entry_of_InA {X : Mx k r} (i j : Fin (2 * r + k + 1)) (h : ∀ n : ℕ, (X ^ (n + 1)) i j = 0) :
    (NormedSpace.exp X) i j = if i = j then 1 else 0 := by sorry
