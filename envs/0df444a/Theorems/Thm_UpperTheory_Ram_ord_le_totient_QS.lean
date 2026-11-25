-- Prove2me | Theorems.Thm_UpperTheory_Ram_ord_le_totient_QS
-- name    : UpperTheory.Ram.ord_le_totient_QS
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:15:27.912622+00:00
-- url     : https://prove2.me/theorems/cbd13d85-b73c-47a0-ace0-d12da883755c
-- title:
--   Ram: ord le totient QS
-- statement:
--   The Ram construction uses the ord le totient QS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/OrdLeTotientQS.lean#L5-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/OrdLeTotientQS.lean#L5-L9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_OrdLeQS
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_OrdLeTotientQS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Ram.ord_le_totient_QS :
    ∀ {φ : Formalism.HC.Frame} (H : Formalism.HC.HostAx φ), φ.ord ≤ H.QS.totient ∧ 2 * φ.ord ≤ H.QS := by sorry
