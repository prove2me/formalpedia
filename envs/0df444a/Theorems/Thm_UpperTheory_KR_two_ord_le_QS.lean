-- Prove2me | Theorems.Thm_UpperTheory_KR_two_ord_le_QS
-- name    : UpperTheory.KR.two_ord_le_QS
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:15:29.906477+00:00
-- url     : https://prove2.me/theorems/0880ad39-1490-4610-8d68-452cdeafec68
-- title:
--   KR: two ord le QS
-- statement:
--   The KR construction uses the two ord le QS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/OrdLeQS.lean#L104-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/OrdLeQS.lean#L104-L157

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_inertQ
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_InertD
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_OrdLeQS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.HF
open Formalism.HC
open scoped Pointwise

theorem UpperTheory.KR.two_ord_le_QS :
    ∀ {φ : Frame} (H : HostAx φ), φ.ord ≤ Nat.totient H.QS ∧ 2 * φ.ord ≤ H.QS ∧ 4 * φ.ord ^ 2 * H.q * H.d ≤ (H.QS * H.q * H.d) ^ 2 := by sorry
