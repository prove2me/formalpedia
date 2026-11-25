-- Prove2me | Theorems.Thm_UpperTheory_Ram_Fun_sum_ceil_nl_le
-- name    : UpperTheory.Ram.Fun.sum_ceil_nl_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:13:27.26101+00:00
-- url     : https://prove2.me/theorems/fa53bfef-bccc-4be5-bbc6-afbe8d86adc9
-- title:
--   Fun: sum ceil nl le
-- statement:
--   The Fun construction uses the sum ceil nl le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FunKit.lean#L51-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FunKit.lean#L51-L73

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

theorem UpperTheory.Ram.Fun.sum_ceil_nl_le (S : Finset ℕ) (n c t : ℕ → ℝ) {K k A B : ℝ} (hK : 0 ≤ K) (hk : 0 ≤ k)
    (hc : ∀ l ∈ S, 0 ≤ c l) (ht : ∀ l ∈ S, t l ≤ 3 / 2) (hn0 : ∀ l ∈ S, 0 ≤ n l)
    (hn : ∀ l ∈ S, n l = 0 ∨ n l = K * c l + k * (2 * c l + 1 + t l))
    (hA : ∑ l ∈ S, c l * Real.log l ≤ A) (hB : ∑ l ∈ S, Real.log l ≤ B) :
    ∑ l ∈ S, ((⌈n l⌉₊ : ℕ) : ℝ) * Real.log l ≤ (K + 2 * k) * A + (5 / 2 * k + 1) * B := by sorry
