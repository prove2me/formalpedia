-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qo8_exists_supported
-- name    : UpperTheory.Reformulated.B.Qo8.exists_supported
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:04:41.50103+00:00
-- url     : https://prove2.me/theorems/5d7e2f31-50dd-49bc-8ca9-1ec64600b258
-- title:
--   Qo8: exists supported
-- statement:
--   The Qo8 construction uses the exists supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsSupported.lean#L3-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsSupported.lean#L3-L31

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsSupported
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qo8.exists_supported :
    ∀ {F : Type} [inst : Field F] [NumberField F]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
    ∃ (π : NumberField.RingOfIntegers F),
      π ≠ (0 : NumberField.RingOfIntegers F) ∧
        π ∈ p.asIdeal ∧
          ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), v ≠ p → π ∉ v.asIdeal := by sorry
