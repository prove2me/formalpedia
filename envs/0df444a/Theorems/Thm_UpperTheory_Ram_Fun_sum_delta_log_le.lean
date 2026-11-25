-- Prove2me | Theorems.Thm_UpperTheory_Ram_Fun_sum_delta_log_le
-- name    : UpperTheory.Ram.Fun.sum_delta_log_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:22:57.186098+00:00
-- url     : https://prove2.me/theorems/00b97222-e718-4a06-97ef-f4e808e6981d
-- title:
--   Fun: sum delta log le
-- statement:
--   The Fun construction uses the sum delta log le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FunKit.lean#L33-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FunKit.lean#L33-L49

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsPrimeOfDifferentLe
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FunKit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset
noncomputable section
open UpperTheory UpperTheory.Ram UpperTheory.Ram.Fun

theorem UpperTheory.Ram.Fun.sum_delta_log_le (E : Type) [Field E] [NumberField E] (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) :
    ∑ l ∈ S, (padicValInt l (discr E) : ℝ) / (Module.finrank ℚ E : ℝ) * Real.log l ≤
      Real.log (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) := by sorry
