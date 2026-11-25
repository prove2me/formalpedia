-- Prove2me | Theorems.Thm_UpperTheory_Ram_Fun_sum_log_le_of_dvd
-- name    : UpperTheory.Ram.Fun.sum_log_le_of_dvd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:11:38.143938+00:00
-- url     : https://prove2.me/theorems/c9df7359-afd0-59e2-8d5f-1548f1febf04
-- title:
--   Fun: sum log le of dvd
-- statement:
--   The Fun construction uses the sum log le of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FunKit.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FunKit.lean#L25-L31

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

theorem UpperTheory.Ram.Fun.sum_log_le_of_dvd {n : ℕ} (hn : n ≠ 0) (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime ∧ l ∣ n) :
    ∑ l ∈ S, Real.log l ≤ Real.log n := by sorry
