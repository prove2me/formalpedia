-- Prove2me | Theorems.Thm_UpperTheory_HF_card_imgOne_dvd
-- name    : UpperTheory.HF.card_imgOne_dvd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:55:34.987498+00:00
-- url     : https://prove2.me/theorems/4004086e-599e-4f7b-9e53-7c5022ecac6c
-- title:
--   HF: card img One dvd
-- statement:
--   The HF construction uses the card img One dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/CardImgOneDvd.lean#L33-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/CardImgOneDvd.lean#L33-L55

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_CardImgOneDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.card_imgOne_dvd :
    ∀ {φ : Frame} (H : HostRaw φ) {f g : ℕ}, f ∣ g → g ∣ H.condN → Nat.card (H.imgOne f) ∣ Nat.card (H.imgOne g) * (g.totient / f.totient) := by sorry
