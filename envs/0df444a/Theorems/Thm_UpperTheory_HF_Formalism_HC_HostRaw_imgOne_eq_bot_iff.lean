-- Prove2me | Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_imgOne_eq_bot_iff
-- name    : UpperTheory.HF.Formalism.HC.HostRaw.imgOne_eq_bot_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:55:39.132564+00:00
-- url     : https://prove2.me/theorems/8154d2b0-a3c5-4992-8c66-b5879c0b68d9
-- title:
--   Host Raw: img One eq bot iff
-- statement:
--   The Host Raw construction uses the img One eq bot iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/DiffDefs.lean#L55-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/DiffDefs.lean#L55-L60

import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SlopeTestRemainingChoices
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open UpperTheory UpperTheory.HF UpperTheory.HF.Formalism UpperTheory.HF.Formalism.HC UpperTheory.HF.Formalism.HC.HostRaw
open UpperTheory.HF _root_.Formalism _root_.Formalism.HC _root_.Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)

theorem UpperTheory.HF.Formalism.HC.HostRaw.imgOne_eq_bot_iff {f : ℕ} (hf : f ∣ H.condN) :
    H.imgOne f = ⊥ ↔ ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD f] → H.art u = 1 := by sorry
