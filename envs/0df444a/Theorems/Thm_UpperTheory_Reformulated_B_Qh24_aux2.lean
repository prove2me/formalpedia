-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qh24_aux2
-- name    : UpperTheory.Reformulated.B.Qh24.aux2
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:32:25.187895+00:00
-- url     : https://prove2.me/theorems/d33eee11-9845-546d-96c6-1ab033d42c1b
-- title:
--   Qh24: aux2
-- statement:
--   The Qh24 construction uses the aux2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InclR.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InclR.lean#L9-L15

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InclR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qh24.aux2 :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F]
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
      SubsemiringClass (ValuationSubring (IsDedekindDomain.HeightOneSpectrum.adicCompletion F v))
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion F v) := by sorry
