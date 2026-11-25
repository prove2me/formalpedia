-- Prove2me | Theorems.Thm_UpperTheory_Ram_Fun_exists_prime_of_different_le
-- name    : UpperTheory.Ram.Fun.exists_prime_of_different_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:45:48.953616+00:00
-- url     : https://prove2.me/theorems/c74bd27d-570c-48e2-8c09-9f69d6108a89
-- title:
--   Fun: exists prime of different le
-- statement:
--   The Fun construction uses the exists prime of different le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FunKit.lean#L85-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FunKit.lean#L85-L87

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsPrimeOfDifferentLe
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FunKit
import Theorems.Thm_UpperTheory_Reformulated_B_Qj12_exists_prime_of_different_le

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
open Formalism.BasicNotions
variable {R : Ranks} (H : Host R)

theorem UpperTheory.Ram.Fun.exists_prime_of_different_le (v : HeightOneSpectrum (𝓞 H.F)) (hle : differentIdeal ℤ (𝓞 H.F) ≤ v.asIdeal) :
    ∃ p : ℕ, p.Prime ∧ p ∣ H.QS * H.q * H.d ∧ (p : 𝓞 H.F) ∈ v.asIdeal := by sorry
