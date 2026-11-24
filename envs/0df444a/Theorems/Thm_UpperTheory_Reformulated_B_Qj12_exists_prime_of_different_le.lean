-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qj12_exists_prime_of_different_le
-- name    : UpperTheory.Reformulated.B.Qj12.exists_prime_of_different_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:28:45.354481+00:00
-- url     : https://prove2.me/theorems/98a93352-e368-48a0-b5b0-1402612150c1
-- title:
--   Qj12: exists prime of different le
-- statement:
--   The Qj12 construction uses the exists prime of different le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsPrimeOfDifferentLe.lean#L8-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsPrimeOfDifferentLe.lean#L8-L27

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsPrimeOfDifferentLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
attribute [local instance] Subfield.toField._proof_1 SubfieldClass.toField._proof_12 SubringClass.toRing._proof_8

theorem UpperTheory.Reformulated.B.Qj12.exists_prime_of_different_le :
    ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥H.F)),
    differentIdeal ℤ (NumberField.RingOfIntegers ↥H.F) ≤ v.asIdeal →
      ∃ (p : ℕ),
        Nat.Prime p ∧
          p ∣ H.QS * H.q * H.d ∧
            (↑p : NumberField.RingOfIntegers ↥H.F) ∈
              v.asIdeal := by sorry
