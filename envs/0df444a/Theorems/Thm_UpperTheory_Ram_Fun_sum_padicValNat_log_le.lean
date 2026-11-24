-- Prove2me | Theorems.Thm_UpperTheory_Ram_Fun_sum_padicValNat_log_le
-- name    : UpperTheory.Ram.Fun.sum_padicValNat_log_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:45:10.257085+00:00
-- url     : https://prove2.me/theorems/58e9f40c-e6a9-4876-8b0a-a86ea2e38034
-- title:
--   Fun: sum padic Val Nat log le
-- statement:
--   The Fun construction uses the sum padic Val Nat log le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FunKit.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FunKit.lean#L11-L23

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

theorem UpperTheory.Ram.Fun.sum_padicValNat_log_le {n : ℕ} (hn : n ≠ 0) (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) :
    ∑ l ∈ S, (padicValNat l n : ℝ) * Real.log l ≤ Real.log n := by sorry
